---- MODULE sync_scheduler ----
(*
Zcash block-download scheduler specification.

Models the inventory-routing registry and download pipeline that sit one layer
above the per-connection protocol in protocol.tla. Where protocol.tla models a
single connection pulling blocks from one partner, this module models the node
choosing which of many peers to ask for each block — the layer where Zebra's
genesis-to-tip sync stall lived (ZcashFoundation/zebra#10679, symptom #5709).

A local syncer downloads blocks 1..MaxBlock from a pool of peers. Each peer
genuinely holds some blocks (Holders); requesting a block a peer does not have
yields an explicit notfound, while any request may also fail transiently
(timeout or dropped connection). The scheduler keeps an availability registry
and only routes a getdata to a peer not already marked missing for that block.

Two booleans select Zebra's pre- and post-fix behaviour:

  BuggyRouting = TRUE  -> a transient error marks the peer missing for the
                          block, poisoning the routing registry.
               = FALSE -> a transient error leaves the entry unknown.

  BuggyDrop    = TRUE  -> a notfound silently drops the block from the work
                          set, wedging the frontier.
               = FALSE -> a notfound re-queues the block (bounded retries),
                          routed away from the notfound peer.

The safety invariant RegistryHonest and the liveness property
EventuallyAllVerified both hold under the fixed behaviour and are violated
under the buggy behaviour, reproducing the stall as a TLC counterexample.

See documents/sync-stall-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT Peers           \* set of peer ids
CONSTANT MaxBlock        \* blocks to download are 1..MaxBlock
CONSTANT LaggingPeers    \* peers that are behind: they hold only blocks 1..LagTip
CONSTANT LagTip          \* chain height of a lagging peer (< MaxBlock)
CONSTANT MaxRetries      \* bound on re-queue attempts per block after a notfound
CONSTANT BuggyRouting    \* TRUE reproduces the registry-poisoning bug
CONSTANT BuggyDrop       \* TRUE reproduces the silent-drop bug

Blocks == 1..MaxBlock
NONE == "none"   \* sentinel for "no peer"; must not be a member of Peers

\* Ground truth: a lagging peer holds blocks up to LagTip; every other peer is
\* at tip and holds them all. The scheduler never reads this directly — it
\* learns a peer's contents only through deliver/notfound. A degraded peer set
\* (most peers lagging) is what made the stall visible in practice.
PeerTip(p) == IF p \in LaggingPeers THEN LagTip ELSE MaxBlock
Holds(p, b) == b <= PeerTip(p)

VARIABLES
    verified,   \* subset of Blocks downloaded and verified (the frontier)
    pending,    \* subset of Blocks the scheduler still wants and may request
    inflight,   \* [ Blocks -> Peers \cup {NONE} ] peer a block is requested from
    avail,      \* [ Peers -> [ Blocks -> {"has","missing","unknown"} ] ] registry
    retries     \* [ Blocks -> 0..MaxRetries ] re-queue attempts used

vars == << verified, pending, inflight, avail, retries >>

----

Init ==
    /\ verified = {}
    /\ pending  = Blocks
    /\ inflight = [ b \in Blocks |-> NONE ]
    /\ avail    = [ p \in Peers |-> [ b \in Blocks |-> "unknown" ] ]
    /\ retries  = [ b \in Blocks |-> 0 ]

\* The scheduler routes a getdata for a pending block to a peer not already
\* marked missing for it (peer-to-candidate choice over the un-poisoned peers).
Request ==
    \E b \in pending:
        \E p \in Peers:
            /\ inflight[b] = NONE
            /\ avail[p][b] # "missing"
            /\ inflight' = [ inflight EXCEPT ![b] = p ]
            /\ pending'  = pending \ {b}
            /\ UNCHANGED << verified, avail, retries >>

\* The in-flight peer genuinely has the block: it is delivered and verified, and
\* the registry correctly records that the peer has it.
DeliverBlock ==
    \E b \in Blocks:
        /\ inflight[b] # NONE
        /\ Holds(inflight[b], b)
        /\ verified' = verified \cup {b}
        /\ avail'    = [ avail EXCEPT ![inflight[b]][b] = "has" ]
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ UNCHANGED << pending, retries >>

\* The in-flight peer genuinely lacks the block and says so. Marking the peer
\* missing for this block is correct — an explicit notfound. What the scheduler
\* does with the block then is the BuggyDrop switch: drop it, or re-queue it
\* (under the retry bound) so it is routed to a different peer next time.
NotFound ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ ~Holds(p, b)
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ avail'    = [ avail EXCEPT ![p][b] = "missing" ]
        /\ IF ~BuggyDrop /\ retries[b] < MaxRetries
           THEN /\ pending' = pending \cup {b}
                /\ retries' = [ retries EXCEPT ![b] = @ + 1 ]
           ELSE /\ UNCHANGED pending   \* silent drop (buggy), or retries exhausted
                /\ UNCHANGED retries
        /\ UNCHANGED verified

\* Any in-flight request may fail transiently (timeout or dropped connection),
\* independent of whether the peer has the block. The request is abandoned and
\* the block re-queued; the BuggyRouting switch decides the registry entry —
\* poisoned (missing) or left unknown.
TransientError ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ pending'  = pending \cup {b}
        /\ avail'    = [ avail EXCEPT ![p][b] = IF BuggyRouting THEN "missing" ELSE "unknown" ]
        /\ UNCHANGED << verified, retries >>

----

Next ==
    \/ Request
    \/ DeliverBlock
    \/ NotFound
    \/ TransientError

\* Strong fairness on the progress actions encodes the real-world assumption
\* that the node keeps trying and a willing peer eventually responds. The
\* transient error gets no fairness — it is adversarial but never forced.
Spec ==
    Init
    /\ [][Next]_vars
    /\ SF_vars(Request)
    /\ SF_vars(DeliverBlock)
    /\ SF_vars(NotFound)

----

\* Liveness: every block is eventually downloaded and verified. The genesis-to-tip
\* stall is a violation of this property.
EventuallyAllVerified == <> (verified = Blocks)

----
\* Safety invariants.

TypeOK ==
    /\ verified \subseteq Blocks
    /\ pending  \subseteq Blocks
    /\ inflight \in [ Blocks -> Peers \cup {NONE} ]
    /\ avail    \in [ Peers -> [ Blocks -> {"has", "missing", "unknown"} ] ]
    /\ retries  \in [ Blocks -> 0..MaxRetries ]

\* The registry never marks a peer missing for a block it actually holds.
\* This is the formal statement of "a timeout is not a notfound": under
\* BuggyRouting a transient error on a holder violates it immediately.
RegistryHonest ==
    \A p \in Peers:
        \A b \in Blocks:
            avail[p][b] = "missing" => ~Holds(p, b)

\* A peer is only ever recorded as having a block it genuinely holds.
RegistryHasIsSound ==
    \A p \in Peers:
        \A b \in Blocks:
            avail[p][b] = "has" => Holds(p, b)

\* A verified block was genuinely available from some peer.
VerifiedAreReal ==
    \A b \in verified:
        \E p \in Peers: Holds(p, b)

====
