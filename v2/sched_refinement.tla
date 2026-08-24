---- MODULE sched_refinement ----
(*
sync_scheduler.tla refines the downloader abstraction.

The mapping forgets the registry, the retry bookkeeping and the peer
identities: the scheduler's verified set is the abstract verified set, and
the blocks routed to some peer are the abstract in-flight set. Request maps
to Request, DeliverBlock to Deliver, and every non-delivery outcome —
NotFound, Refused, Truncated, Timeout — to Requeue; Reconnect stutters.

TLC checks D!Spec as a property of the scheduler's Spec. The check passes
for the fixed AND the buggy configurations alike: the stall bugs are
liveness bugs, invisible at this altitude — which is exactly what the
common abstraction is for (shared pipeline structure, per-model liveness).
*)
EXTENDS sync_scheduler

AbsInflight == { b \in Blocks : inflight[b] # NONE }

D == INSTANCE downloader WITH verified <- verified,
                              inflight <- AbsInflight,
                              MaxBlock <- MaxBlock

RefinesDownloader == D!Spec

====
