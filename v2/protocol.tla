---- MODULE protocol ----
(*
Version 2 Zcash P2P protocol specification, following the draft ZIP
"Version 2 Zcash P2P Network Protocol" (zcash/zips#1344).

Models connection setup and block synchronization over the stream layer of
streams.tla: the init handshake on the dedicated handshake stream, protocol
version negotiation, the long-lived block announcement streams (including
the rule that at most one announcement stream of a type may be open per
direction and the sender's option to replace a finished or reset stream),
and headers-first synchronization over get-headers and get-blocks request
streams, each carrying exactly one request and its response.

Blocks are heights on one linear chain: only the peer at the highest height
extends it, and a peer that is behind downloads the heights it lacks.

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

Peers in ByzantinePeers complete an honest handshake and may then commit
wire-level mischief: a second init record, a stream of unknown type, a
record of unknown kind on the handshake stream, and a stream finished
before its type byte. The receiver's obligations differ per the draft: the
first and last are connection errors, the middle two MUST be tolerated
(forward compatibility). Ghost flags record genuine violations so that
CloseAccountable can check no honest receiver ever fires PROTOCOL_ERROR
without one, and EventuallyPunished that every violation ends the
connection.

Under StrictSingleton the invariant NoHonestProtocolError is violated: two
conformant peers disconnect because stream independence lets a replacement
stream's type byte arrive before the old stream's FIN or reset.

See documents/v2-modeling.md for the full write-up.
*)

EXTENDS TLC, Naturals, Sequences, FiniteSets, streams, records

CONSTANT InitialPeers        \* set of peers
CONSTANT MaxBlock            \* maximum block height (initial and mined)
CONSTANT MaxRestarts         \* finish/reset of own announcement streams, per peer pair
CONSTANT MaxHeaders          \* headers per get-headers response (draft: 160)
CONSTANT MaxBlocksPerRequest \* hashes per get-blocks request (draft: 128)
CONSTANT MinVersion          \* minimum protocol version of the draft (not yet assigned)
CONSTANT Versions            \* protocol versions a peer may advertise
CONSTANT StrictSingleton     \* see module comment
CONSTANT RefusePreHandshake  \* see module comment
CONSTANT ByzantinePeers      \* peers that may misbehave after an honest handshake
CONSTANT MaxMischief         \* Byzantine actions available per peer pair
CONSTANT PunishUnknownType   \* TRUE closes on unknown stream types (buggy)

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
            want       |-> [ j \in OtherPeers[i] |-> <<>> ],
            score      |-> [ j \in OtherPeers[i] |-> 0 ],
            mischief   |-> [ j \in OtherPeers[i] |-> 0 ],
            violated   |-> [ j \in OtherPeers[i] |-> FALSE ],
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

\* Request streams n has outstanding toward m.
OpenReq(n, m) == { sid \in StreamIds(n, m) :
                     /\ sid[1] = n
                     /\ S(n, m, sid).status = "open"
                     /\ S(n, m, sid).rtype \in RequestTypes }

\* The sequence of heights a..b (empty when b < a).
Range(a, b) == [ i \in 1..(b - a + 1) |-> a + i - 1 ]

Contiguous(seq) == \A i \in 1..(Len(seq) - 1) : seq[i + 1] = seq[i] + 1

\* Heights of seq above h.
Above(seq, h) == SelectSeq(seq, LAMBDA x : x > h)

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
\*   any other stream before n's handshake completed-> refuse with REFUSED, or wait (RefusePreHandshake)
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
                   \/ /\ t \notin StreamTypes
                      \* Unknown stream type: refuse with
                      \* UNSUPPORTED_STREAM_TYPE; the draft says MUST NOT
                      \* close or penalize — new stream types deploy
                      \* without version gating. PunishUnknownType is the
                      \* forbidden reading.
                      /\ \/ /\ PunishUnknownType
                            /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                         \/ /\ ~PunishUnknownType
                            /\ nodes' = Settle([ nodes EXCEPT
                                     ![n].streams[m][sid] = ClosedStream,
                                     ![m].streams[n][sid] = Refuse(@, t, "UNSUPPORTED_STREAM_TYPE") ],
                                   n, m, sid)
                   \/ /\ t \in StreamTypes
                      /\ \/ /\ t = HandshakeType
                            /\ \/ /\ legalHs
                                  /\ nodes' = accept
                               \/ /\ ~legalHs
                                  /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                         \/ /\ t \in AnnTypes \cup RequestTypes
                            /\ \/ /\ ~HandshakeComplete(n, m)
                                  /\ RefusePreHandshake
                                  /\ nodes' = Settle([ nodes EXCEPT
                                           ![n].streams[m][sid] = ClosedStream,
                                           ![m].streams[n][sid] = Refuse(@, t, "REFUSED") ],
                                         n, m, sid)
                               \/ /\ HandshakeComplete(n, m)
                                  /\ \/ /\ t \in AnnTypes /\ StrictSingleton /\ dup
                                        /\ nodes' = Close(nodes, n, m, "PROTOCOL_ERROR")
                                     \/ /\ ~(t \in AnnTypes /\ StrictSingleton /\ dup)
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

\* n ignores a record of unknown kind on the handshake stream: "a node MUST
\* ignore handshake-stream records whose kind it does not recognize"
\* (draft: "Connection Handshake").
RecvUnknownHandshakeRecord ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in HandshakeStreams(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ Len(s.inq) > 0
                /\ s.inq[1].kind \notin { "init", "type", "fin" }
                /\ nodes' = [ nodes EXCEPT ![n].streams[m][sid].inq = Tail(@) ]

----

\* --- Byzantine actions ---
\* A Byzantine peer completes an honest handshake and then misbehaves at
\* the wire level, within a MaxMischief budget. Ghost bookkeeping: the
\* HONEST side's `violated` flag records genuine violations (the first and
\* last are; the tolerated two are not), so accountability is checkable.

ByzCan(n, m) ==
    /\ n \in ByzantinePeers
    /\ Connected(n, m)
    /\ HandshakeComplete(n, m)
    /\ nodes[n].mischief[m] < MaxMischief

\* A second init record on the handshake stream — a violation the receiver
\* MUST answer with PROTOCOL_ERROR (draft: "Handshake Validation").
ByzSecondInit ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in HandshakeStreams(n, m):
                /\ ByzCan(n, m)
                /\ nodes' = [ nodes EXCEPT
                        ![m].streams[n][sid] = PutData(@, MakeInit(nodes[n].my_version, Height(n))),
                        ![n].mischief[m]     = @ + 1,
                        ![m].violated[n]     = TRUE ]

\* A record of unknown kind on the handshake stream — NOT a violation:
\* future revisions may define new kinds and the receiver MUST ignore them.
ByzUnknownHandshakeRecord ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in HandshakeStreams(n, m):
                /\ ByzCan(n, m)
                /\ nodes' = [ nodes EXCEPT
                        ![m].streams[n][sid] = PutData(@, [ kind |-> "junk" ]),
                        ![n].mischief[m]     = @ + 1 ]

\* A stream of a type the receiver does not recognize — NOT a violation:
\* the receiver refuses it with UNSUPPORTED_STREAM_TYPE and moves on
\* (draft: "Stream Types").
ByzUnknownStreamType ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ ByzCan(n, m)
            /\ FreeSlots(n, m) # {}
            /\ LET sid == << n, FreeSlot(n, m) >>
               IN nodes' = [ nodes EXCEPT
                    ![n].streams[m][sid] = ClosedStream,
                    ![m].streams[n][sid] = PeerStream("0xEE", <<>>),
                    ![n].mischief[m]     = @ + 1 ]

\* A handshake stream opened by a peer that already has one (or is the
\* responder) — a violation the receiver MUST answer with PROTOCOL_ERROR
\* (draft: "Connection Handshake").
ByzSecondHandshakeStream ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ ByzCan(n, m)
            /\ FreeSlots(n, m) # {}
            /\ LET sid == << n, FreeSlot(n, m) >>
               IN nodes' = [ nodes EXCEPT
                    ![n].streams[m][sid] = ClosedStream,
                    ![m].streams[n][sid] = PeerStream(HandshakeType, <<>>),
                    ![n].mischief[m]     = @ + 1,
                    ![m].violated[n]     = TRUE ]

\* A stream finished before a complete type byte — a violation the receiver
\* MUST answer with PROTOCOL_ERROR (draft: "Stream Types").
ByzEarlyFin ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ ByzCan(n, m)
            /\ FreeSlots(n, m) # {}
            /\ LET sid == << n, FreeSlot(n, m) >>
               IN nodes' = [ nodes EXCEPT
                    ![n].streams[m][sid] = ClosedStream,
                    ![m].streams[n][sid] = [ NullStream EXCEPT !.status = "open",
                                                               !.inq = << FIN >> ],
                    ![n].mischief[m]     = @ + 1,
                    ![m].violated[n]     = TRUE ]

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

\* --- Request streams: headers-first synchronization ---

\* n is behind m (from m's init or announcements), has nothing queued to
\* download and no request outstanding: it asks m for headers after its own
\* tip (draft: "Headers-First Synchronization", step 1). The request and the
\* FIN of n's sending direction are written together.
SendGetHeaders ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Connected(n, m)
            /\ HandshakeComplete(n, m)
            /\ nodes[n].peer_tip[m] > Height(n)
            /\ nodes[n].want[m] = <<>>
            /\ OpenReq(n, m) = {}
            /\ FreeSlots(n, m) # {}
            /\ LET sid == << n, FreeSlot(n, m) >>
               IN nodes' = [ nodes EXCEPT
                    ![n].streams[m][sid] = RequesterStream(GetHeadersType),
                    ![m].streams[n][sid] = PeerStream(GetHeadersType,
                                              << MakeGetHeaders(Height(n)), FIN >>) ]

\* n serves a get-headers request from m: the headers after the locator, at
\* most MaxHeaders of them, then FIN. Serving may start as soon as the
\* request is complete, before m's FIN has been consumed (draft: "Request
\* Streams").
ServeGetHeaders ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ HandshakeComplete(n, m)
                /\ s.status = "open"
                /\ s.rtype = GetHeadersType
                /\ s.out = "open"
                /\ Len(s.inq) > 0
                /\ Head(s.inq).kind = "get-headers"
                /\ LET loc  == Head(s.inq).locator
                       hdrs == Range(loc + 1, Min(loc + MaxHeaders, Height(n)))
                   IN nodes' = [ nodes EXCEPT
                        ![n].streams[m][sid] = Collapse([ @ EXCEPT !.inq = Tail(@),
                                                                   !.out = "finished" ]),
                        ![m].streams[n][sid] = PutData(PutData(@, MakeHeaders(hdrs)), FIN) ]

\* n consumes a headers response from m (draft: "get-headers"):
\*   more than MaxHeaders, or not contiguous -> discard, misbehavior penalty
\*   otherwise                               -> queue the heights n lacks
RecvHeaders ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in OpenReq(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ s.rtype = GetHeadersType
                /\ Len(s.inq) > 0
                /\ Head(s.inq).kind = "headers"
                /\ LET hdrs == Head(s.inq).heights
                   IN
                   \/ /\ Len(hdrs) <= MaxHeaders /\ Contiguous(hdrs)
                      /\ nodes' = [ nodes EXCEPT
                              ![n].streams[m][sid].inq = Tail(@),
                              ![n].want[m]             = Above(hdrs, Height(n)) ]
                   \/ /\ ~(Len(hdrs) <= MaxHeaders /\ Contiguous(hdrs))
                      /\ nodes' = [ nodes EXCEPT
                              ![n].streams[m][sid].inq = Tail(@),
                              ![n].score[m]            = @ + 20 ]

\* n requests the next batch of blocks it wants from m, at most
\* MaxBlocksPerRequest of them (draft: "get-blocks").
SendGetBlocks ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Connected(n, m)
            /\ nodes[n].want[m] # <<>>
            /\ OpenReq(n, m) = {}
            /\ FreeSlots(n, m) # {}
            /\ LET sid   == << n, FreeSlot(n, m) >>
                   batch == SubSeq(nodes[n].want[m], 1,
                                   Min(MaxBlocksPerRequest, Len(nodes[n].want[m])))
               IN nodes' = [ nodes EXCEPT
                    ![n].streams[m][sid] = RequesterStream(GetBlocksType),
                    ![m].streams[n][sid] = PeerStream(GetBlocksType,
                                              << MakeGetBlocks(batch), FIN >>) ]

\* n serves a get-blocks request from m. It may finish after any complete
\* entry, delivering fewer blocks than requested (draft: "get-blocks"); the
\* requester re-requests the remainder.
ServeGetBlocks ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in StreamIds(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ HandshakeComplete(n, m)
                /\ s.status = "open"
                /\ s.rtype = GetBlocksType
                /\ s.out = "open"
                /\ Len(s.inq) > 0
                /\ Head(s.inq).kind = "get-blocks"
                /\ LET asked == Head(s.inq).heights
                       held  == SelectSeq(asked, LAMBDA h : h \in nodes[n].blocks)
                   IN
                   \E k \in 1..Len(held) :
                       nodes' = [ nodes EXCEPT
                            ![n].streams[m][sid] = Collapse([ @ EXCEPT !.inq = Tail(@),
                                                                       !.out = "finished" ]),
                            ![m].streams[n][sid] = PutData(PutData(@, MakeBlocks(SubSeq(held, 1, k))), FIN) ]

\* n consumes delivered blocks from m and extends its chain with them.
RecvBlocks ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            \E sid \in OpenReq(n, m):
                LET s == S(n, m, sid)
                IN
                /\ Connected(n, m)
                /\ s.rtype = GetBlocksType
                /\ Len(s.inq) > 0
                /\ Head(s.inq).kind = "blocks"
                /\ LET got    == Head(s.inq).heights
                       blocks == nodes[n].blocks \cup { got[i] : i \in 1..Len(got) }
                   IN nodes' = [ nodes EXCEPT
                        ![n].streams[m][sid].inq = Tail(@),
                        ![n].blocks              = blocks,
                        ![n].want[m]             = Above(nodes[n].want[m], Cardinality(blocks)) ]

----

\* --- Stream teardown ---

\* n consumes a FIN: the peer's sending direction is over, and the stream
\* closes once n's own direction is too. On a request stream the FIN may
\* arrive after the response was already served; it is never "data after a
\* complete request". A FIN before the type byte, or on the handshake
\* stream, is handled per the draft (PROTOCOL_ERROR; graceful close)
\* although honest peers never produce either.
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
                   \/ /\ s.rtype \in AnnTypes \cup RequestTypes
                      /\ nodes' = Settle([ nodes EXCEPT
                              ![n].streams[m][sid] = Collapse([ @ EXCEPT !.inq = Tail(@),
                                                                         !.in_done = TRUE ]) ],
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

\* The peer at the chain tip finds a new block, giving it something to
\* announce. Only the highest peer extends the chain, which keeps the model a
\* single linear chain that the others catch up with.
MineBlock ==
    \E n \in InitialPeers:
        /\ Height(n) < MaxBlock
        /\ \A m \in OtherPeers[n] : Height(m) <= Height(n)
        /\ nodes' = [ nodes EXCEPT ![n].blocks = @ \cup { Height(n) + 1 } ]

----

Next ==
    \/ Connect
    \/ OpenHandshakeStream
    \/ SendInitResponder
    \/ RecvTypeByte
    \/ RecvInit
    \/ RecvUnknownHandshakeRecord
    \/ ByzSecondInit
    \/ ByzUnknownHandshakeRecord
    \/ ByzUnknownStreamType
    \/ ByzSecondHandshakeStream
    \/ ByzEarlyFin
    \/ OpenAnnouncementStream
    \/ SendAnnouncement
    \/ RecvAnnouncement
    \/ FinishAnnouncementStream
    \/ ResetAnnouncementStream
    \/ SendGetHeaders
    \/ ServeGetHeaders
    \/ RecvHeaders
    \/ SendGetBlocks
    \/ ServeGetBlocks
    \/ RecvBlocks
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

\* Eventually all peers hold the same chain.
EventualConsensus ==
    <>[] \A i, j \in InitialPeers : nodes[i].blocks = nodes[j].blocks

----

\* --- Safety invariants ---

TypeOK ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        /\ nodes[n].conn[m] \in { "none", "initiator", "responder", "closed" }
        /\ nodes[n].close[m] \in ErrorCodes \cup { NoCode }
        /\ nodes[n].version[m] \in Versions \cup { 0 }
        /\ nodes[n].restarts[m] \in 0..MaxRestarts
        /\ nodes[n].score[m] \in Nat
        /\ nodes[n].mischief[m] \in 0..MaxMischief
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

\* Blocks are always a contiguous chain from genesis.
BlocksContiguous ==
    \A n \in InitialPeers : nodes[n].blocks = 1..Height(n)

\* Request streams are only opened after the handshake completes, one at a
\* time per peer (draft: "Connection Handshake"; ZIP-204 in-transit limit).
RequestsAfterHandshake ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        /\ OpenReq(n, m) # {} => HandshakeComplete(n, m)
        /\ Cardinality(OpenReq(n, m)) <= 1

\* Responses in flight respect the draft's bounds: at most MaxHeaders
\* contiguous headers, at most MaxBlocksPerRequest hashes per get-blocks.
ResponsesBounded ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] : \A sid \in StreamIds(n, m) :
        \A i \in 1..Len(S(n, m, sid).inq) :
            LET x == S(n, m, sid).inq[i]
            IN /\ x.kind = "headers"    => Len(x.heights) <= MaxHeaders /\ Contiguous(x.heights)
               /\ x.kind = "get-blocks" => Len(x.heights) <= MaxBlocksPerRequest
               /\ x.kind = "blocks"     => Len(x.heights) <= MaxBlocksPerRequest

\* Honest peers never earn a misbehavior penalty.
NoHonestPenalty ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] : nodes[n].score[m] = 0

\* No interleaving of conformant behaviour ends in a protocol error. Checked
\* in configurations with no Byzantine peers, where any close other than
\* OBSOLETE is a disagreement between honest peers about the draft's rules.
NoHonestProtocolError ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        nodes[n].close[m] \in { NoCode, "OBSOLETE" }

\* Accountability: an honest receiver fires PROTOCOL_ERROR only after a
\* genuine violation by the peer. Tolerated mischief (unknown stream types,
\* unknown handshake records) never sets the ghost flag, so a receiver that
\* punished it would violate this invariant.
CloseAccountable ==
    \A n \in InitialPeers \ ByzantinePeers : \A m \in OtherPeers[n] :
        nodes[n].close[m] = "PROTOCOL_ERROR" => nodes[n].violated[m]

\* Every genuine violation eventually ends the connection.
EventuallyPunished ==
    \A n \in InitialPeers : \A m \in OtherPeers[n] :
        [] (nodes[n].violated[m] => <> (nodes[n].conn[m] = "closed"))

====
