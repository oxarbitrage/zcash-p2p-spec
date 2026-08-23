---- MODULE streams ----
(*
The stream layer of the version 2 Zcash P2P protocol (draft ZIP,
zcash/zips#1344, "Stream Layer"), as realised by QUIC.

A connection carries many streams. Each stream is reliable and ordered on its
own, but streams are mutually independent: data on one stream is never
delayed by another (draft: "Transport Requirements"). The model therefore
keeps one in-flight queue PER STREAM rather than one inbox per connection as
the legacy model does; delivery picks any stream, which yields every
cross-stream interleaving the transport allows.

Two control signals can overtake queued data in QUIC and are modeled as flags
rather than queue elements: RESET_STREAM (`in_reset`, sent by the peer on its
own sending direction) and STOP_SENDING (`stop`, the peer asking us to stop
sending). FIN is ordered after the data it follows and is a queue sentinel.

This module defines data shapes and pure helpers only; the actions live in
protocol.tla.
*)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxStreams     \* stream slots per opener per connection

----

\* Stream types (draft: "Stream Types"). The type is the first byte written
\* on every stream; the receiver learns it only by consuming that byte.
HandshakeType == "0x00"     \* bidirectional, initiator only, exactly one
BlockAnnType  == "0x10"     \* unidirectional, long-lived
AnnTypes      == { BlockAnnType }
StreamTypes   == { HandshakeType } \cup AnnTypes
BidiTypes     == { HandshakeType }

\* Application error codes (draft: "Application Error Codes").
ErrorCodes == { "NO_ERROR", "PROTOCOL_ERROR", "UNSUPPORTED_STREAM_TYPE",
                "OBSOLETE", "SELF_CONNECTION", "FLOOD", "MISBEHAVIOR",
                "CANCELLED", "REFUSED", "INTERNAL_ERROR" }
NoCode == "none"

\* Every queue element is a record with a `kind` field so that TLC can
\* compare them: the type byte that opens a stream, the FIN sentinel of a
\* finished sending direction, and the protocol records of records.tla.
TypeByte(t) == [ kind |-> "type", t |-> t ]
FIN         == [ kind |-> "fin" ]

\* Stream identifiers for the connection between n and m: who opened it, and
\* a slot number. Slots are reused once both peers have closed the stream.
StreamIds(n, m) == { n, m } \X (1..MaxStreams)

----

\* A peer's local view of one stream. Queued data flows TOWARD the owner of
\* the record: a sender appends to the remote peer's record, exactly as the
\* legacy model appends to the remote inbox.
\*
\*   status   "none" (slot free) | "open" | "closed" (done locally, peer may not be)
\*   rtype    stream type once known; "unknown" until the type byte is consumed
\*   inq      data in flight toward this peer, FIN-terminated when finished
\*   in_reset error code of a RESET_STREAM from the peer, observable any time
\*   out      this peer's own sending direction: "open" | "finished" | "reset" | "na"
\*   stop     error code of a STOP_SENDING from the peer for our direction
NullStream == [ status   |-> "none",
                rtype    |-> "unknown",
                inq      |-> <<>>,
                in_reset |-> NoCode,
                out      |-> "na",
                stop     |-> NoCode ]

\* A locally closed stream collapses to one canonical record so that the
\* state space does not retain the history of how it was closed.
ClosedStream == [ NullStream EXCEPT !.status = "closed" ]

\* The opener's record of a stream it just opened with type t.
OpenerStream(t) == [ status   |-> "open",
                     rtype    |-> t,
                     inq      |-> <<>>,
                     in_reset |-> NoCode,
                     out      |-> "open",
                     stop     |-> NoCode ]

\* The remote peer's record of the same stream: the type byte is the first
\* queued element, followed by any records written at open time.
PeerStream(t, payload) == [ status   |-> "open",
                            rtype    |-> "unknown",
                            inq      |-> << TypeByte(t) >> \o payload,
                            in_reset |-> NoCode,
                            out      |-> IF t \in BidiTypes THEN "open" ELSE "na",
                            stop     |-> NoCode ]

\* Transport-side delivery helpers. Writes to a stream the receiver has
\* already closed are dropped, as QUIC discards data after STOP_SENDING.
PutData(s, x)     == IF s.status = "open" THEN [ s EXCEPT !.inq = Append(@, x) ] ELSE s
PutReset(s, code) == IF s.status = "open" THEN [ s EXCEPT !.in_reset = code ] ELSE s
PutStop(s, code)  == IF s.status = "open" THEN [ s EXCEPT !.stop = code ] ELSE s

\* Head-of-queue classification.
IsTypeByte(x) == x.kind = "type"
IsFin(x)      == x.kind = "fin"

====
