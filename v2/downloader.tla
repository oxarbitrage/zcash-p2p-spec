---- MODULE downloader ----
(*
The download pipeline abstraction.

The minimal object both v2 sync models are about: a set of verified blocks
and a set of blocks in flight. A block is requested (enters flight),
delivered (leaves flight into verified), or requeued (leaves flight with
nothing — timeout, refusal, truncation, not-found, a closed connection);
the chain can also be extended directly (mining). Verified blocks are a
contiguous prefix of the chain and are never lost.

protocol.tla (the concrete stream-level protocol) and sync_scheduler.tla
(the peer-choosing scheduler) both refine this module — see refinement.tla
and sched_refinement.tla. The refinement is over safety only: it ties the
pipeline structure of the two models together, saying nothing about
fairness or liveness, which each model states in its own terms. In
particular the buggy scheduler configurations still refine this module —
the stall bugs are liveness bugs, invisible at this altitude.
*)
EXTENDS Naturals, FiniteSets

CONSTANT MaxBlock    \* the chain is 1..MaxBlock

Blocks == 1..MaxBlock

VARIABLES
    verified,   \* blocks held and verified: always a prefix 1..k
    inflight    \* blocks currently being downloaded

vars == << verified, inflight >>

----

\* Download may begin anywhere in the chain: the pipeline may already hold a
\* verified prefix (a node is born with at least the genesis block, or with
\* nothing when the scheduler starts from scratch).
Init ==
    /\ \E k \in 0..MaxBlock : verified = 1..k
    /\ inflight = {}

\* A block neither held nor in flight is requested.
Request ==
    \E b \in Blocks \ (verified \cup inflight):
        /\ inflight' = inflight \cup { b }
        /\ UNCHANGED verified

\* An in-flight block is delivered and verified.
Deliver ==
    \E b \in inflight:
        /\ verified' = verified \cup { b }
        /\ inflight' = inflight \ { b }

\* An in-flight block comes back with nothing: timeout, refusal, truncation,
\* not-found, or the connection carrying it closed.
Requeue ==
    \E b \in inflight:
        /\ inflight' = inflight \ { b }
        /\ UNCHANGED verified

\* The chain is extended without a download (mining at the tip).
Extend ==
    \E b \in Blocks \ (verified \cup inflight):
        /\ verified' = verified \cup { b }
        /\ UNCHANGED inflight

----

Next == Request \/ Deliver \/ Requeue \/ Extend

Spec == Init /\ [][Next]_vars

----

TypeOK ==
    /\ verified \subseteq Blocks
    /\ inflight \subseteq Blocks

\* A block is never both held and in flight.
Disjoint == verified \cap inflight = {}

====
