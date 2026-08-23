---- MODULE protocol ----
(*
Version 2 Zcash P2P protocol specification, following the draft ZIP
"Version 2 Zcash P2P Network Protocol" (zcash/zips#1344).

Phase 1 models connection setup over the stream layer of streams.tla:
the init handshake on the dedicated handshake stream, protocol version
negotiation, and the long-lived block announcement streams, including the
rule that at most one announcement stream of a type may be open per
direction and the sender's option to replace a finished or reset stream.

Communication keeps the legacy model's message consumption discipline: a peer
decides only from its own records; the only place both peers' records are
written together is the transport itself (connection open/close, stream
open, and the freeing of a stream slot once both sides have closed it).

Two boolean constants select how a receiver interprets the draft:

    StrictSingleton      TRUE  a second open announcement stream of the same
                               type from a peer is a PROTOCOL_ERROR (literal
                               reading of "Announcement Streams")
                         FALSE the receiver accepts it and drains both
    RefusePreHandshake   TRUE  announcement streams that arrive before the
                               local handshake completes are refused with
                               REFUSED ("Connection Handshake": MAY refuse)
                         FALSE they are buffered until it completes

Under StrictSingleton the invariant NoHonestProtocolError is violated: two
conformant peers disconnect because stream independence lets a replacement
stream's type byte arrive before the old stream's FIN or reset.

See documents/v2-modeling.md for the full write-up.
*)

EXTENDS TLC, Naturals, Sequences, FiniteSets, streams, records

CONSTANT InitialPeers        \* set of peers
CONSTANT MaxBlock            \* maximum block height (initial and mined)
CONSTANT MaxRestarts         \* finish/reset of own announcement streams, per peer pair
CONSTANT MinVersion          \* minimum protocol version of the draft (not yet assigned)
CONSTANT Versions            \* protocol versions a peer may advertise
CONSTANT StrictSingleton     \* see module comment
CONSTANT RefusePreHandshake  \* see module comment

VARIABLE nodes

----
vars == << nodes >>

\* See README for an explanation of symmetry reduction.
Symmetry == Permutations(InitialPeers)

\* For each initial peer construct a set of all other peers.
OtherPeers == [ n \in InitialPeers |-> InitialPeers \ { n } ]

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

Init ==
    \E blockset \in [ InitialPeers -> (1..MaxBlock) ] :
    \E verset   \in [ InitialPeers -> Versions ] :
        nodes = [ i \in InitialPeers |-> [
            conn       |-> [ j \in OtherPeers[i] |-> "none" ],
            close      |-> [ j \in OtherPeers[i] |-> NoCode ],
            streams    |-> [ j \in OtherPeers[i] |-> [ sid \in StreamIds(i, j) |-> NullStream ] ],
            init_sent  |-> [ j \in OtherPeers[i] |-> FALSE ],
            init_recvd |-> [ j \in OtherPeers[i] |-> FALSE ],
            version    |-> [ j \in OtherPeers[i] |-> 0 ],
            peer_tip   |-> [ j \in OtherPeers[i] |-> 0 ],
            announced  |-> [ j \in OtherPeers[i] |-> 0 ],
            restarts   |-> [ j \in OtherPeers[i] |-> 0 ],
            blocks     |-> 1..blockset[i],
            my_version |-> verset[i]
        ]]

----

\* --- Helpers ---

Height(n) == Cardinality(nodes[n].blocks)

Connected(n, m) == nodes[n].conn[m] \in { "initiator", "responder" }

\* The handshake is complete for n once it has both sent and received an
\* init record (draft: "Handshake Sequence", step 3).
HandshakeComplete(n, m) == nodes[n].init_sent[m] /\ nodes[n].init_recvd[m]

S(n, m, sid) == nodes[n].streams[m][sid]

\* Slots n may use to open a new stream toward m (lowest free slot is taken).
FreeSlots(n, m) == { k \in 1..MaxStreams : S(n, m, << n, k >>).status = "none" }
FreeSlot(n, m)  == CHOOSE k \in FreeSlots(n, m) : \A j \in FreeSlots(n, m) : k <= j

\* Announcement streams of type t that n currently sends to m on.
LiveAnn(n, m, t) == { sid \in StreamIds(n, m) :
                        /\ sid[1] = n
                        /\ S(n, m, sid).status = "open"
                        /\ S(n, m, sid).rtype = t
                        /\ S(n, m, sid).out = "open" }

\* Handshake streams n knows about on its connection with m.
HandshakeStreams(n, m) == { sid \in StreamIds(n, m) :
                              /\ S(n, m, sid).status = "open"
                              /\ S(n, m, sid).rtype = HandshakeType }

\* Transport: once both peers have closed a stream its slot is freed.
Settle(ns, n, m, sid) ==
    IF /\ ns[n].streams[m][sid].status = "closed"
       /\ ns[m].streams[n][sid].status = "closed"
    THEN [ ns EXCEPT ![n].streams[m][sid] = NullStream,
                     ![m].streams[n][sid] = NullStream ]
    ELSE ns

\* Transport: n closes the connection to m with an application error code.
\* Both peers observe the close; data in flight is lost.
Close(ns, n, m, code) ==
    [ ns EXCEPT ![n].conn[m]    = "closed",
                ![n].close[m]   = code,
                ![n].streams[m] = [ sid \in StreamIds(n, m) |-> NullStream ],
                ![m].conn[n]    = "closed",
                ![m].close[n]   = code,
                ![m].streams[n] = [ sid \in StreamIds(n, m) |-> NullStream ] ]

----

\* --- Connection ---

\* n dials m. The QUIC handshake is out of scope and establishment is atomic:
\* n becomes the initiator and m the responder of the application handshake.
Connect ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "none"
            /\ nodes[m].conn[n] = "none"
            /\ nodes' = [ nodes EXCEPT ![n].conn[m] = "initiator",
                                       ![m].conn[n] = "responder" ]

----

\* --- Handshake ---

\* The initiator opens the handshake stream and sends its init record on it
\* (draft: "Handshake Sequence", step 1). The type byte and the record are
\* queued together: they travel in order on the same stream.
OpenHandshakeStream ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "initiator"
            /\ ~nodes[n].init_sent[m]
            /\ FreeSlots(n, m) # {}
            /\ LET sid == << n, FreeSlot(n, m) >>
               IN nodes' = [ nodes EXCEPT
                    ![n].streams[m][sid] = OpenerStream(HandshakeType),
                    ![m].streams[n][sid] = PeerStream(HandshakeType,
                                              << MakeInit(nodes[n].my_version, Height(n)) >>),
                    ![n].init_sent[m]    = TRUE ]

\* The responder sends its own init record on the handshake stream. It may do
\* so as soon as it has seen the stream's type byte, without waiting for the
\* initiator's init record (draft: "Handshake Sequence").
SendInitResponder ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in HandshakeStreams(n, m):
                /\ nodes[n].conn[m] = "responder"
                /\ ~nodes[n].init_sent[m]
                /\ nodes' = [ nodes EXCEPT
                        ![m].streams[n][sid] = PutData(@, MakeInit(nodes[n].my_version, Height(n))),
                        ![n].init_sent[m]    = TRUE ]

\* n consumes the type byte of a stream m opened. What happens depends on the
\* type and on n's own state:
\*   0x00 from the responder, or a second 0x00      -> PROTOCOL_ERROR ("Connection Handshake")
\*   announcement before n's handshake completed    -> refuse with REFUSED, or wait (RefusePreHandshake)
\*   announcement duplicating an open one of type t -> PROTOCOL_ERROR, or accept (StrictSingleton)
\*   otherwise                                      -> record the type
RecvTypeByte ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ s.status = "open"
                /\ s.rtype = "unknown"
                /\ Len(s.inq) > 0
                /\ IsTypeByte(Head(s.inq))
                /\ LET t      == Head(s.inq).t
                       accept == [ nodes EXCEPT ![n].streams[m][sid].rtype = t,
                                                ![n].streams[m][sid].inq   = Tail(@) ]
                       legalHs == nodes[n].conn[m] = "responder" /\ HandshakeStreams(n, m) = {}
                       dup    == \E o \in StreamIds(n, m) :
                                    /\ o # sid
                                    /\ o[1] = m
                                    /\ S(n, m, o).status = "open"
                                    /\ S(n, m, o).rtype = t
                   IN
                   /\ t \in StreamTypes
                   /\ \/ /\ t = HandshakeType
                         /\ \/ /\ legalHs
                               /\ nodes' = accept
                            \/ /\ ~legalHs
                               /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                      \/ /\ t \in AnnTypes
                         /\ \/ /\ ~HandshakeComplete(n, m)
                               /\ RefusePreHandshake
                               /\ nodes' = Settle([ nodes EXCEPT
                                        ![n].streams[m][sid] = ClosedStream,
                                        ![m].streams[n][sid] = PutStop(@, "REFUSED") ],
                                      n, m, sid)
                            \/ /\ HandshakeComplete(n, m)
                               /\ \/ /\ StrictSingleton /\ dup
                                     /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                                  \/ /\ ~(StrictSingleton /\ dup)
                                     /\ nodes' = accept

\* n consumes m's init record from the handshake stream (draft: "Handshake
\* Validation"):
\*   second init record          -> PROTOCOL_ERROR
\*   version below MinVersion    -> OBSOLETE
\*   otherwise                   -> handshake received; negotiated version = min
RecvInit ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in HandshakeStreams(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ Len(s.inq) > 0
                /\ Head(s.inq).kind = "init"
                /\ LET msg == Head(s.inq)
                   IN
                   \/ /\ nodes[n].init_recvd[m]
                      /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                   \/ /\ ~nodes[n].init_recvd[m]
                      /\ msg.version < MinVersion
                      /\ nodes' = Close(nodes, n, m, "OBSOLETE")
                   \/ /\ ~nodes[n].init_recvd[m]
                      /\ msg.version >= MinVersion
                      /\ nodes' = [ nodes EXCEPT
                              ![n].streams[m][sid].inq = Tail(@),
                              ![n].init_recvd[m]       = TRUE,
                              ![n].version[m]          = Min(nodes[n].my_version, msg.version),
                              ![n].peer_tip[m]         = msg.start_height ]

----

\* --- Announcement streams ---

\* After its handshake completes, n opens one announcement stream of each
\* type it has none open for (draft: "Announcement Streams"). This is also
\* how a replacement is opened after a finish, reset, or refusal. A reset
\* can overtake announcements still in flight, so the sender forgets what it
\* announced and re-announces its tip on the new stream.
OpenAnnouncementStream ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E t \in AnnTypes:
                /\ Connected(n, m)
                /\ HandshakeComplete(n, m)
                /\ LiveAnn(n, m, t) = {}
                /\ FreeSlots(n, m) # {}
                /\ LET sid == << n, FreeSlot(n, m) >>
                   IN nodes' = [ nodes EXCEPT
                        ![n].streams[m][sid] = OpenerStream(t),
                        ![m].streams[n][sid] = PeerStream(t, <<>>),
                        ![n].announced[m]    = 0 ]

\* n announces its current tip to m when it has grown since the last
\* announcement (draft: "Block Announcements", header announcement).
SendAnnouncement ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in LiveAnn(n, m, BlockAnnType):
                /\ nodes[n].announced[m] < Height(n)
                /\ nodes' = [ nodes EXCEPT
                        ![m].streams[n][sid] = PutData(@, MakeHeaderAnnouncement(Height(n))),
                        ![n].announced[m]    = Height(n) ]

\* n consumes a header announcement from m. Announcements are only processed
\* once n's handshake is complete (draft: "Connection Handshake").
RecvAnnouncement ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ HandshakeComplete(n, m)
                /\ s.status = "open"
                /\ s.rtype \in AnnTypes
                /\ Len(s.inq) > 0
                /\ Head(s.inq).kind = "header"
                /\ nodes' = [ nodes EXCEPT
                        ![n].streams[m][sid].inq = Tail(@),
                        ![n].peer_tip[m]         = Max(@, Head(s.inq).height) ]

\* n finishes one of its announcement streams. The draft allows a sender to
\* open a replacement afterwards; why it finished (backpressure, internal
\* restart) is not modeled. Bounded by MaxRestarts to keep liveness meaningful.
FinishAnnouncementStream ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in LiveAnn(n, m, BlockAnnType):
                /\ nodes[n].restarts[m] < MaxRestarts
                /\ nodes' = Settle([ nodes EXCEPT
                        ![n].streams[m][sid] = ClosedStream,
                        ![m].streams[n][sid] = PutData(@, FIN),
                        ![n].restarts[m]     = @ + 1 ],
                      n, m, sid)

\* Same as FinishAnnouncementStream but via RESET_STREAM, which can overtake
\* records still in flight on that stream.
ResetAnnouncementStream ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in LiveAnn(n, m, BlockAnnType):
                /\ nodes[n].restarts[m] < MaxRestarts
                /\ nodes' = Settle([ nodes EXCEPT
                        ![n].streams[m][sid] = ClosedStream,
                        ![m].streams[n][sid] = PutReset(@, "INTERNAL_ERROR"),
                        ![n].restarts[m]     = @ + 1 ],
                      n, m, sid)

----

\* --- Stream teardown ---

\* n consumes a FIN. A FIN before the type byte, or on the handshake stream,
\* is handled per the draft (PROTOCOL_ERROR; graceful close) although honest
\* peers in this phase never produce either.
RecvFin ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ s.status = "open"
                /\ Len(s.inq) > 0
                /\ IsFin(Head(s.inq))
                /\ \/ /\ s.rtype = "unknown"
                      /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                   \/ /\ s.rtype = HandshakeType
                      /\ nodes' = Close(nodes, n, m, "NO_ERROR")
                   \/ /\ s.rtype \in AnnTypes
                      /\ nodes' = Settle([ nodes EXCEPT ![n].streams[m][sid] = ClosedStream ],
                                         n, m, sid)

\* n observes a RESET_STREAM from m. Queued data on that stream is discarded.
RecvReset ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ s.status = "open"
                /\ s.in_reset # NoCode
                /\ \/ /\ s.rtype = HandshakeType
                      /\ nodes' = Close(nodes, n, m, "NO_ERROR")
                   \/ /\ s.rtype # HandshakeType
                      /\ nodes' = Settle([ nodes EXCEPT ![n].streams[m][sid] = ClosedStream ],
                                         n, m, sid)

\* n observes a STOP_SENDING from m on a stream n is sending on, and resets
\* its sending direction as the draft recommends ("Request Streams").
RecvStop ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ sid[1] = n
                /\ s.status = "open"
                /\ s.out = "open"
                /\ s.stop # NoCode
                /\ nodes' = Settle([ nodes EXCEPT
                        ![n].streams[m][sid] = ClosedStream,
                        ![m].streams[n][sid] = PutReset(@, s.stop) ],
                      n, m, sid)

----

\* --- Chain growth ---

\* n finds a new block, giving it something to announce.
MineBlock ==
    \E n \in InitialPeers:
        /\ Height(n) < MaxBlock
        /\ nodes' = [ nodes EXCEPT ![n].blocks = @ \cup { Height(n) + 1 } ]

----

Next ==
    \/ Connect
    \/ OpenHandshakeStream
    \/ SendInitResponder
    \/ RecvTypeByte
    \/ RecvInit
    \/ OpenAnnouncementStream
    \/ SendAnnouncement
    \/ RecvAnnouncement
    \/ FinishAnnouncementStream
    \/ ResetAnnouncementStream
    \/ RecvFin
    \/ RecvReset
    \/ RecvStop
    \/ MineBlock

\* Weak fairness on Next: as long as any action is enabled, one is taken.
\* Mining and restarts are bounded, so every behaviour quiesces and every
\* enabled receive eventually happens. The one loop that is not bounded is a
\* responder refusing pre-handshake announcement streams while the sender
\* keeps reopening them; fairness on RecvInit guarantees the responder
\* eventually processes the init record that ends that loop.
Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ WF_vars(RecvInit)

----

\* --- Liveness ---

\* Every connection eventually completes its handshake (or has been closed).
HandshakeCompletes ==
    <>[] \A n \in InitialPeers : \A m \in OtherPeers[n] :
        nodes[n].conn[m] = "closed" \/ HandshakeComplete(n, m)

\* Every peer eventually learns every connected peer's final tip.
AnnouncementsFlow ==
    <>[] \A n \in InitialPeers : \A m \in OtherPeers[n] :
        nodes[n].conn[m] = "closed" \/ nodes[n].peer_tip[m] = Height(m)

----

\* --- Safety invariants ---

TypeOK ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        /\ nodes[n].conn[m] \in { "none", "initiator", "responder", "closed" }
        /\ nodes[n].close[m] \in ErrorCodes \cup { NoCode }
        /\ nodes[n].version[m] \in Versions \cup { 0 }
        /\ nodes[n].restarts[m] \in 0..MaxRestarts
        /\ \A sid \in StreamIds(n, m) :
            /\ S(n, m, sid).status \in { "none", "open", "closed" }
            /\ S(n, m, sid).rtype \in StreamTypes \cup { "unknown" }
            /\ S(n, m, sid).out \in { "open", "finished", "reset", "na" }

\* A stream slot is free on one side exactly when it is free on the other.
SlotsConsistent ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] : \A sid \in StreamIds(n, m) :
        (S(n, m, sid).status = "none") = (S(m, n, sid).status = "none")

\* At most one handshake stream per connection, opened by the initiator
\* (draft: "Connection Handshake").
OneHandshakeStream ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        /\ Cardinality(HandshakeStreams(n, m)) <= 1
        /\ \A sid \in HandshakeStreams(n, m) :
            IF sid[1] = n THEN nodes[n].conn[m] = "initiator"
                          ELSE nodes[m].conn[n] = "initiator"

\* A peer opens no stream before sending its init record, and no announcement
\* stream before its handshake completes (draft: "Connection Handshake").
HandshakeBeforeStreams ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        /\ ~nodes[n].init_sent[m] =>
            \A k \in 1..MaxStreams : S(n, m, << n, k >>).status = "none"
        /\ ~HandshakeComplete(n, m) =>
            \A k \in 1..MaxStreams : S(n, m, << n, k >>).rtype \notin AnnTypes

\* Once n has received m's init, the negotiated version is the minimum of the
\* two advertised versions (draft: "Protocol Versioning").
NegotiatedVersionIsMin ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        HandshakeComplete(n, m) =>
            nodes[n].version[m] = Min(nodes[n].my_version, nodes[m].my_version)

\* A sender never has two announcement streams of one type open toward a peer
\* (draft: "Announcement Streams").
SenderSingleton ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] : \A t \in AnnTypes :
        Cardinality(LiveAnn(n, m, t)) <= 1

\* OBSOLETE is only ever used against a peer that advertised an old version.
CloseJustified ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        nodes[n].close[m] = "OBSOLETE" =>
            \/ nodes[n].my_version < MinVersion
            \/ nodes[m].my_version < MinVersion

\* No interleaving of conformant behaviour ends in a protocol error. There are
\* no adversarial actions in this phase, so any close other than OBSOLETE is a
\* disagreement between honest peers about the draft's rules.
NoHonestProtocolError ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        nodes[n].close[m] \in { NoCode, "OBSOLETE" }

====
