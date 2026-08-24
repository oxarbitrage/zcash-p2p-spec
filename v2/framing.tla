---- MODULE framing ----
(*
Tor transport stream-framing specification.

The Tor transport carries the stream layer over a SINGLE ordered bytestream
per connection, using a QUIC-modelled framing layer ("Stream Framing"):
STREAM frames append data to streams (FIN flag finishes a direction),
opening is implicit in the first frame of a new stream ID, and flow control
is cumulative — MAX_DATA bounds total bytes across all streams, and
MAX_STREAMS_UNI bounds the total count of opened unidirectional streams,
raised by absolute-valued frames. The initial credits come from the
connection preamble. This is the least implementation-tested text of the
draft: Zebra's framing layer was removed as unreachable code.

The model: a sender S delivers one bulk record of Total bytes on one
stream, and separately keeps one announcement stream open, finishing and
replacing it (as "Announcement Streams" allows and this repository's
Finding 2 recommends), MaxReplace times. Frames travel in order; credit
grants travel back in order. Three policy switches:

  GrantPerRecord        the receiver raises MAX_DATA only after processing
                        a COMPLETE record (record-granularity processing),
                        rather than as bytes arrive.
  RaiseOnClose          the receiver raises MAX_STREAMS_UNI as streams
                        finish, QUIC's way of maintaining a concurrency
                        limit expressed cumulatively.
  SenderReadsConcurrent the sender reads the preamble's stream-limit field
                        as a CONCURRENT limit (the preamble's own word)
                        instead of the cumulative count the framing
                        section defines.

Findings this module reproduces (see ../documents/v2-modeling.md):

  - The draft mandates a minimum initial_max_stream_data that covers a
    maximum record, but sets NO minimum for the connection-level
    initial_max_data. A peer advertising less than one record of
    connection credit, talking to a record-granularity receiver — both
    conforming — wedges the connection forever (framing_wedge.cfg); the
    same credits with byte-granularity granting complete fine
    (framing_perframe.cfg).
  - The preamble calls the stream-limit fields "concurrent"; the framing
    section defines them as cumulative. The two readings are both
    implementable and disagree: a cumulative-reading sender stalls
    silently when the receiver never raises the limit
    (framing_noraise.cfg), and a concurrent-reading sender is disconnected
    with PROTOCOL_ERROR by a cumulative-enforcing receiver
    (framing_concurrent.cfg) — honest peers reading different sentences
    of the same section.
  - StrictSingletonSafeHere: on this transport the announcement-stream
    replacement race of Finding 1 CANNOT occur — the pipe is ordered, so
    the old stream's FIN always precedes the replacement's first frame.
    The literal singleton rule is safe on Tor and unsafe on QUIC, which
    may explain how it was written.
*)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Total                  \* bytes of the bulk record (max record abstracted)
CONSTANT InitMaxData            \* preamble initial_max_data (connection credit)
CONSTANT InitMaxStreamsUni      \* preamble initial_max_streams_uni
CONSTANT MaxReplace             \* announcement stream replacements S performs
CONSTANT GrantPerRecord         \* see module comment
CONSTANT RaiseOnClose           \* see module comment
CONSTANT SenderReadsConcurrent  \* see module comment

BulkSid == 0
AnnSid(k) == k   \* announcement streams are 1..1+MaxReplace, opened in order

VARIABLES
    pipe,        \* ordered frames S -> R
    back,        \* ordered credit frames R -> S
    s_sent,      \* bulk bytes S has sent
    s_data_lim,  \* connection-level credit S may use (last MAX_DATA, cumulative bytes)
    s_str_lim,   \* cumulative count of uni streams S may open (last MAX_STREAMS_UNI)
    s_opened,    \* uni streams S has opened so far
    s_finned,    \* uni streams S has finished so far
    r_delivered, \* bulk bytes R has processed
    r_granted,   \* connection credit R has advertised
    r_str_lim,   \* stream-count limit R has advertised
    r_opened,    \* uni streams R has observed opening
    r_ann_open,  \* announcement sids R sees open (opened, no FIN yet)
    closed       \* "none" | "PROTOCOL_ERROR"

vars == << pipe, back, s_sent, s_data_lim, s_str_lim, s_opened, s_finned,
           r_delivered, r_granted, r_str_lim, r_opened, r_ann_open, closed >>

NoCode == "none"

\* Frames: STREAM open of an announcement stream (length 0, abstracted),
\* its FIN, one bulk data byte, and the two credit-raising frames.
OpenF(k)  == [ t |-> "open",  sid |-> k ]
FinF(k)   == [ t |-> "fin",   sid |-> k ]
ByteF     == [ t |-> "byte",  sid |-> BulkSid ]
MaxDataF(m)    == [ t |-> "max_data",    max |-> m ]
MaxStreamsF(m) == [ t |-> "max_streams", max |-> m ]

----

Init ==
    /\ pipe = <<>> /\ back = <<>>
    /\ s_sent = 0 /\ s_data_lim = InitMaxData
    /\ s_str_lim = InitMaxStreamsUni /\ s_opened = 0 /\ s_finned = 0
    /\ r_delivered = 0 /\ r_granted = InitMaxData
    /\ r_str_lim = InitMaxStreamsUni /\ r_opened = 0 /\ r_ann_open = {}
    /\ closed = NoCode

\* S sends the next byte of the bulk record, within the connection credit
\* its peer has granted (the per-stream credit never binds: the draft
\* mandates initial_max_stream_data of at least a full record).
SendBulkByte ==
    /\ closed = NoCode
    /\ s_sent < Total
    /\ s_sent < s_data_lim
    /\ s_sent' = s_sent + 1
    /\ pipe' = Append(pipe, ByteF)
    /\ UNCHANGED << back, s_data_lim, s_str_lim, s_opened, s_finned,
                    r_delivered, r_granted, r_str_lim, r_opened, r_ann_open, closed >>

\* S opens its announcement stream, or a replacement after finishing the
\* previous one. What "within the stream limit" means is the switch: the
\* cumulative count the framing section defines, or the concurrent count
\* the preamble's field description suggests.
OpenAnn ==
    /\ closed = NoCode
    /\ s_opened = s_finned              \* previous announcement stream finished
    /\ s_opened <= MaxReplace           \* the initial stream plus MaxReplace replacements
    /\ IF SenderReadsConcurrent
       THEN (s_opened - s_finned) < s_str_lim
       ELSE s_opened < s_str_lim
    /\ s_opened' = s_opened + 1
    /\ pipe' = Append(pipe, OpenF(AnnSid(s_opened + 1)))
    /\ UNCHANGED << back, s_sent, s_data_lim, s_str_lim, s_finned,
                    r_delivered, r_granted, r_str_lim, r_opened, r_ann_open, closed >>

\* S finishes its open announcement stream, intending to replace it.
FinAnn ==
    /\ closed = NoCode
    /\ s_opened = s_finned + 1
    /\ s_finned' = s_finned + 1
    /\ pipe' = Append(pipe, FinF(AnnSid(s_opened)))
    /\ UNCHANGED << back, s_sent, s_data_lim, s_str_lim, s_opened,
                    r_delivered, r_granted, r_str_lim, r_opened, r_ann_open, closed >>

\* R processes the next frame, in order. A bulk byte may trigger a MAX_DATA
\* raise (immediately, or only once the record is complete, per the
\* switch); an open is checked against the cumulative stream limit and the
\* strict singleton reading; a FIN may trigger a MAX_STREAMS raise.
RecvFrame ==
    /\ closed = NoCode
    /\ pipe # <<>>
    /\ LET f == Head(pipe) IN
       \/ /\ f.t = "byte"
          /\ r_delivered' = r_delivered + 1
          /\ LET done  == r_delivered + 1 >= Total
                 grant == IF GrantPerRecord THEN done ELSE TRUE
             IN /\ r_granted' = IF grant THEN Total ELSE r_granted
                /\ back' = IF grant /\ r_granted < Total
                           THEN Append(back, MaxDataF(Total)) ELSE back
          /\ pipe' = Tail(pipe)
          /\ UNCHANGED << s_sent, s_data_lim, s_str_lim, s_opened, s_finned,
                          r_str_lim, r_opened, r_ann_open, closed >>
       \/ /\ f.t = "open"
          /\ \/ /\ r_opened + 1 > r_str_lim
                \* the framing section's cumulative limit is exceeded:
                \* a connection error of type PROTOCOL_ERROR
                /\ closed' = "PROTOCOL_ERROR"
                /\ UNCHANGED << pipe, back, s_sent, s_data_lim, s_str_lim,
                                s_opened, s_finned, r_delivered, r_granted,
                                r_str_lim, r_opened, r_ann_open >>
             \/ /\ r_opened + 1 <= r_str_lim
                /\ r_opened' = r_opened + 1
                /\ r_ann_open' = r_ann_open \cup { f.sid }
                /\ pipe' = Tail(pipe)
                /\ UNCHANGED << back, s_sent, s_data_lim, s_str_lim, s_opened,
                                s_finned, r_delivered, r_granted, r_str_lim, closed >>
       \/ /\ f.t = "fin"
          /\ r_ann_open' = r_ann_open \ { f.sid }
          /\ LET raise == RaiseOnClose
             IN /\ r_str_lim' = IF raise THEN r_str_lim + 1 ELSE r_str_lim
                /\ back' = IF raise THEN Append(back, MaxStreamsF(r_str_lim + 1)) ELSE back
          /\ pipe' = Tail(pipe)
          /\ UNCHANGED << s_sent, s_data_lim, s_str_lim, s_opened, s_finned,
                          r_delivered, r_granted, r_opened, closed >>

\* S processes the next credit frame; limits never decrease.
RecvBack ==
    /\ closed = NoCode
    /\ back # <<>>
    /\ LET f == Head(back) IN
       /\ s_data_lim' = IF f.t = "max_data" /\ f.max > s_data_lim THEN f.max ELSE s_data_lim
       /\ s_str_lim'  = IF f.t = "max_streams" /\ f.max > s_str_lim THEN f.max ELSE s_str_lim
    /\ back' = Tail(back)
    /\ UNCHANGED << pipe, s_sent, s_opened, s_finned,
                    r_delivered, r_granted, r_str_lim, r_opened, r_ann_open, closed >>

----

Next == SendBulkByte \/ OpenAnn \/ FinAnn \/ RecvFrame \/ RecvBack

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

\* Liveness: the bulk record is eventually delivered, and every replacement
\* announcement stream eventually opens.
BulkDelivered == <> (r_delivered = Total)
ReplacementsComplete == <> (s_opened = MaxReplace + 1)

----
\* Safety invariants.

TypeOK ==
    /\ s_sent \in 0..Total /\ r_delivered \in 0..Total
    /\ s_opened \in 0..(MaxReplace + 1) /\ s_finned \in 0..s_opened
    /\ closed \in { NoCode, "PROTOCOL_ERROR" }

\* Finding 1's race is impossible on this transport: the pipe is ordered,
\* so a replacement's open frame is never observed before the previous
\* stream's FIN — the receiver never sees two announcement streams open.
StrictSingletonSafeHere == Cardinality(r_ann_open) <= 1

\* No interleaving of these conforming-but-divergent peers should end in a
\* protocol error.
NoHonestProtocolError == closed = NoCode

====
