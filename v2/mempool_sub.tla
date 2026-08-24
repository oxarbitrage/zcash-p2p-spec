---- MODULE mempool_sub ----
(*
get-mempool subscription lifecycle specification.

The draft ("get-mempool") makes the mempool stream the one open-ended
request stream: the responder streams a snapshot and then updates until the
stream or connection ends; a requester that no longer wants the subscription
cancels the responder's sending direction with CANCELLED. And: "A node MUST
NOT open more than one concurrent `get-mempool` stream to the same peer; a
second concurrent subscription is a connection error of type
`PROTOCOL_ERROR`."

The cancel and a re-subscription travel on different streams, and streams
are mutually independent ("Transport Requirements"), so the responder can
observe the new subscription's type byte before the old subscription's
cancel. At that moment it is serving one stream and sees a second — from a
requester that, from its own point of view, never had two subscriptions at
once. This is the announcement-stream replacement race (see protocol.tla,
Finding 1) recurring in a second rule of the draft.

The StrictSub constant selects the reading:

    TRUE    a second subscription observed while one is being served is a
            connection error (the literal text). NoHonestProtocolError is
            violated.
    FALSE   the responder treats the old subscription as cancelled (its
            cancel is on the way), ends it, and serves the new one. All
            properties hold.

Zebra's draft implementation is strict: `mempool_subscribed.swap(true)`
fails the connection on a second subscription, and the flag is cleared only
when serving ends — its conformance notes call the mitigation "prompt
cancel detection", i.e. timing. Its own requester keeps one subscription
per connection and never re-subscribes after a cancel, so Zebra-to-Zebra
does not reach the race; the draft explicitly anticipates cancel/re-open
churn from other requesters (it recommends rate-limiting it, which is a
FLOOD-coded answer to a liveness problem, not an ordering rule).

The responder-initiated end (finishing the stream on shutdown or snapshot
lag) is not modeled: when the responder ends the stream itself its serving
slot is already free before the requester can react, so that direction has
no race.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT MaxSubs     \* subscription attempts available to the requester
CONSTANT StrictSub   \* see module comment

Slots == 1..MaxSubs

\* One record per subscription attempt k:
\*   r        requester's view: none | open | cancelled | closed
\*   s        responder's view: none (not yet observed) | serving | done
\*   open_if  the stream's type byte is in flight toward the responder
\*   stop_if  the requester's CANCELLED stop-sending is in flight
\*   end_if   the responder's reset/finish is in flight toward the requester
VARIABLES subs, closed

vars == << subs, closed >>

NoCode == "none"

NullSub == [ r |-> "none", s |-> "none",
             open_if |-> FALSE, stop_if |-> FALSE, end_if |-> FALSE ]

FreeSlots == { k \in Slots : subs[k].r = "none" }

----

Init ==
    /\ subs = [ k \in Slots |-> NullSub ]
    /\ closed = NoCode

\* The requester opens a get-mempool stream when it considers itself
\* unsubscribed ("MUST NOT open more than one concurrent stream", judged
\* from its own state — it cannot judge from the responder's).
Subscribe ==
    /\ closed = NoCode
    /\ \A k \in Slots : subs[k].r # "open"
    /\ FreeSlots # {}
    /\ LET k == CHOOSE k \in FreeSlots : \A j \in FreeSlots : k <= j
       IN subs' = [ subs EXCEPT ![k].r = "open", ![k].open_if = TRUE ]
    /\ UNCHANGED closed

\* The requester cancels its live subscription with CANCELLED, intending to
\* re-subscribe (the churn the draft anticipates). Bounded by the free
\* slots so the model quiesces with a live subscription.
Cancel ==
    \E k \in Slots:
        /\ closed = NoCode
        /\ subs[k].r = "open"
        /\ FreeSlots # {}
        /\ subs' = [ subs EXCEPT ![k].r = "cancelled", ![k].stop_if = TRUE ]
        /\ UNCHANGED closed

\* The responder observes attempt k's type byte. If it is still serving an
\* attempt whose cancel it has not yet seen, this looks like a second
\* concurrent subscription:
\*   StrictSub  -> connection error PROTOCOL_ERROR (the literal text)
\*   otherwise  -> the stream the requester opened LATER wins: a newer
\*                 stream supersedes the one being served; an older one is
\*                 the stale open of an already-cancelled subscription,
\*                 observed late, and is refused without penalty.
\*
\* The tolerant rule needs the order in which the PEER opened its streams
\* (slot numbers here; QUIC stream IDs in reality — monotone per opener).
\* A first tolerant attempt that superseded on every open, without
\* consulting the order, failed EventuallySubscribed: opens themselves
\* reorder, so a stale open can arrive after the live subscription's and
\* would supersede it, leaving the requester unsubscribed for good. The
\* draft's abstract stream layer does not expose stream creation order, so
\* the working rule is not implementable against the abstraction as
\* written — only against QUIC directly.
SeeOpen ==
    \E k \in Slots:
        LET dup   == \E j \in Slots : j # k /\ subs[j].s = "serving"
            newer == \A j \in Slots : subs[j].s = "serving" => k > j
        IN
        /\ closed = NoCode
        /\ subs[k].open_if
        /\ \/ /\ StrictSub /\ dup
              /\ closed' = "PROTOCOL_ERROR"
              /\ subs' = [ j \in Slots |-> NullSub ]
           \/ /\ ~StrictSub /\ dup /\ ~newer
              /\ closed' = closed
              /\ subs' = [ subs EXCEPT ![k].s = "done", ![k].open_if = FALSE,
                                        ![k].end_if = TRUE ]
           \/ /\ ~(StrictSub /\ dup) /\ (newer \/ ~dup)
              /\ closed' = closed
              /\ subs' = [ j \in Slots |->
                             IF j = k
                             THEN [ subs[k] EXCEPT !.s = "serving", !.open_if = FALSE ]
                             ELSE IF subs[j].s = "serving"
                             THEN [ subs[j] EXCEPT !.s = "done", !.end_if = TRUE ]
                             ELSE subs[j] ]

\* The responder observes the CANCELLED stop-sending for attempt k and, if
\* it was still serving it, resets the stream and stops the work (draft:
\* "Request Streams"). On an already superseded or unseen attempt the stop
\* changes nothing but is still consumed.
SeeStop ==
    \E k \in Slots:
        /\ closed = NoCode
        /\ subs[k].stop_if
        /\ subs' = [ subs EXCEPT
               ![k].stop_if = FALSE,
               ![k].open_if = FALSE,
               ![k].s       = IF @ = "serving" THEN "done" ELSE @,
               ![k].end_if  = @ \/ subs[k].s = "serving" ]
        /\ UNCHANGED closed

\* The requester observes the responder's reset/finish of attempt k.
RecvEnd ==
    \E k \in Slots:
        /\ closed = NoCode
        /\ subs[k].end_if
        /\ subs' = [ subs EXCEPT ![k].end_if = FALSE,
                                 ![k].r = IF @ \in { "open", "cancelled" } THEN "closed" ELSE @ ]
        /\ UNCHANGED closed

----

Next == Subscribe \/ Cancel \/ SeeOpen \/ SeeStop \/ RecvEnd

\* Per-slot fairness on the responder's and requester's receive actions (the
\* existential form can be discharged by other slots while one starves —
\* see dial.tla), plus fairness on subscribing. Cancel is never forced.
Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Subscribe)
    /\ \A k \in Slots :
           /\ WF_vars(closed = NoCode /\ subs[k].open_if /\ SeeOpen)
           /\ WF_vars(closed = NoCode /\ subs[k].stop_if /\ SeeStop)
           /\ WF_vars(closed = NoCode /\ subs[k].end_if  /\ RecvEnd)

----

\* Liveness: the requester ends up subscribed and served.
EventuallySubscribed ==
    <>[] \E k \in Slots : subs[k].r = "open" /\ subs[k].s = "serving"

----
\* Safety invariants.

TypeOK ==
    /\ subs \in [ Slots -> [ r : { "none", "open", "cancelled", "closed" },
                             s : { "none", "serving", "done" },
                             open_if : BOOLEAN, stop_if : BOOLEAN, end_if : BOOLEAN ] ]
    /\ closed \in { NoCode, "PROTOCOL_ERROR" }

\* The requester's MUST: it never considers two subscriptions open at once.
RequesterSingleton ==
    Cardinality({ k \in Slots : subs[k].r = "open" }) <= 1

\* The responder never serves two streams at once, in either reading.
ResponderSingleton ==
    Cardinality({ k \in Slots : subs[k].s = "serving" }) <= 1

\* No interleaving of conformant behaviour ends in a protocol error.
NoHonestProtocolError == closed = NoCode

====
