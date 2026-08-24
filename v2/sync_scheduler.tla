---- MODULE sync_scheduler ----
(*
Version 2 block-download scheduler specification.

Models the layer above the per-connection protocol in protocol.tla: the node
choosing which peer to ask for each block — the layer where Zebra's
genesis-to-tip sync stall lived in the legacy protocol
(ZcashFoundation/zebra#10679; see ../sync_scheduler.tla). Zebra's v2 stack
defers this layer to a future scheduler ("ibd-engine"), so this module models
it ahead of the implementation.

The v2 protocol gives a request more ways to end without a block than the
legacy protocol did. Only one of them says anything about the peer's chain:

    not-found    the per-entry result 0x02 of get-blocks: an explicit
                 statement that the peer lacks the block.
    REFUSED      the responder reset the stream, declining to serve it
                 (overload, rate limits, Zebra's bulk-stream cap). Says
                 nothing about the peer's chain.
    truncation   the responder finished after any complete entry, leaving
                 later entries unanswered ("get-blocks", "get-block-range").
                 Routine and sanctioned; says nothing about the peer's chain.
    timeout      no response within the stall timeout; the requester cancels
                 with CANCELLED ("Block Download Parameters"). Says nothing
                 about the peer's chain.

Three booleans mark each of the uninformative outcomes as informative, each
reproducing a variant of the legacy registry-poisoning bug:

  TreatRefusedAsMissing    = TRUE -> a REFUSED marks the peer missing
  TreatTruncatedAsMissing  = TRUE -> an unanswered entry marks the peer missing
  BuggyTimeout             = TRUE -> a timeout marks the peer missing
                                     (the exact legacy zebra#10679 bug)

Separately, the scheduler applies Zebra's unresponsive-peer rule: a peer that
times out UnresponsiveLimit requests in a row, with no response of any kind in
between, is disconnected (ZcashFoundation/zebra#11276). The Redial boolean
decides whether disconnected peers are ever redialled; without it, evicting
the only holder of a block stalls the sync even though every registry entry
is honest.

RegistryHonest and EventuallyAllVerified hold with every switch in its fixed
position (Redial = TRUE, the rest FALSE) and are violated under the buggy
settings, each as a short TLC counterexample.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT Peers                    \* set of peer ids
CONSTANT MaxBlock                 \* blocks to download are 1..MaxBlock
CONSTANT LaggingPeers             \* peers that hold only blocks 1..LagTip
CONSTANT LagTip                   \* chain height of a lagging peer (< MaxBlock)
CONSTANT MaxRetries               \* bound on re-queue attempts per block after a notfound
CONSTANT UnresponsiveLimit        \* consecutive timeouts before a peer is disconnected
CONSTANT TreatRefusedAsMissing    \* TRUE treats a REFUSED as a notfound (buggy)
CONSTANT TreatTruncatedAsMissing  \* TRUE treats an unanswered entry as a notfound (buggy)
CONSTANT BuggyTimeout             \* TRUE treats a timeout as a notfound (legacy bug)
CONSTANT Redial                   \* TRUE redials disconnected peers

Blocks == 1..MaxBlock
NONE == "none"   \* sentinel for "no peer"; must not be a member of Peers

\* Ground truth: a lagging peer holds blocks up to LagTip; every other peer is
\* at tip and holds them all. The scheduler never reads this directly — it
\* learns a peer's contents only through the outcomes below.
PeerTip(p) == IF p \in LaggingPeers THEN LagTip ELSE MaxBlock
Holds(p, b) == b <= PeerTip(p)

VARIABLES
    verified,   \* subset of Blocks downloaded and verified (the frontier)
    pending,    \* subset of Blocks the scheduler still wants and may request
    inflight,   \* [ Blocks -> Peers \cup {NONE} ] peer a block is requested from
    avail,      \* [ Peers -> [ Blocks -> {"has","missing","unknown"} ] ] registry
    retries,    \* [ Blocks -> 0..MaxRetries ] re-queue attempts used
    timeouts,   \* [ Peers -> 0..UnresponsiveLimit ] consecutive unanswered timeouts
    connected   \* [ Peers -> BOOLEAN ] FALSE once disconnected as unresponsive

vars == << verified, pending, inflight, avail, retries, timeouts, connected >>

----

Init ==
    /\ verified  = {}
    /\ pending   = Blocks
    /\ inflight  = [ b \in Blocks |-> NONE ]
    /\ avail     = [ p \in Peers |-> [ b \in Blocks |-> "unknown" ] ]
    /\ retries   = [ b \in Blocks |-> 0 ]
    /\ timeouts  = [ p \in Peers |-> 0 ]
    /\ connected = [ p \in Peers |-> TRUE ]

\* The scheduler opens a get-blocks request for a pending block toward a
\* connected peer not already marked missing for it.
Request ==
    \E b \in pending:
        \E p \in Peers:
            /\ inflight[b] = NONE
            /\ connected[p]
            /\ avail[p][b] # "missing"
            /\ inflight' = [ inflight EXCEPT ![b] = p ]
            /\ pending'  = pending \ {b}
            /\ UNCHANGED << verified, avail, retries, timeouts, connected >>

\* The in-flight peer genuinely has the block: it is delivered and verified.
\* Any response resets the peer's consecutive-timeout count.
DeliverBlock ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ Holds(p, b)
        /\ verified' = verified \cup {b}
        /\ avail'    = [ avail EXCEPT ![p][b] = "has" ]
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ timeouts' = [ timeouts EXCEPT ![p] = 0 ]
        /\ UNCHANGED << pending, retries, connected >>

\* The in-flight peer genuinely lacks the block and answers the entry with the
\* explicit not-found result. This is the one outcome that legitimately marks
\* the registry, and the block is re-queued (bounded) toward other peers.
NotFound ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ ~Holds(p, b)
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ avail'    = [ avail EXCEPT ![p][b] = "missing" ]
        /\ timeouts' = [ timeouts EXCEPT ![p] = 0 ]
        /\ IF retries[b] < MaxRetries
           THEN /\ pending' = pending \cup {b}
                /\ retries' = [ retries EXCEPT ![b] = @ + 1 ]
           ELSE /\ UNCHANGED pending   \* retries exhausted
                /\ UNCHANGED retries
        /\ UNCHANGED << verified, connected >>

\* The responder resets the request stream with REFUSED — it declines to serve
\* the request, whether or not it holds the block (draft: "Request Streams";
\* Zebra refuses beyond 2 concurrent bulk streams). A REFUSED is a response,
\* so the timeout count resets; what it does to the registry is the
\* TreatRefusedAsMissing switch.
Refused ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ pending'  = pending \cup {b}
        /\ timeouts' = [ timeouts EXCEPT ![p] = 0 ]
        /\ avail'    = [ avail EXCEPT ![p][b] =
                            IF TreatRefusedAsMissing THEN "missing" ELSE @ ]
        /\ UNCHANGED << verified, retries, connected >>

\* The responder finishes the stream early, leaving this entry unanswered
\* (draft: "get-blocks" / "get-block-range" allow finishing after any complete
\* entry; truncation is resumable). Sanctioned and routine — but uninformative
\* about the peer's chain. The registry effect is the TreatTruncatedAsMissing
\* switch.
Truncated ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ inflight' = [ inflight EXCEPT ![b] = NONE ]
        /\ pending'  = pending \cup {b}
        /\ timeouts' = [ timeouts EXCEPT ![p] = 0 ]
        /\ avail'    = [ avail EXCEPT ![p][b] =
                            IF TreatTruncatedAsMissing THEN "missing" ELSE @ ]
        /\ UNCHANGED << verified, retries, connected >>

\* No response within the stall timeout: the requester cancels the stream with
\* CANCELLED and re-queues the block (draft: "Block Download Parameters").
\* The registry effect is the BuggyTimeout switch — the exact legacy bug.
\* The peer's consecutive-timeout count rises; at UnresponsiveLimit the peer
\* is disconnected as unresponsive (Zebra's rule).
Timeout ==
    \E b \in Blocks:
        LET p == inflight[b] IN
        /\ p # NONE
        /\ inflight'  = [ inflight EXCEPT ![b] = NONE ]
        /\ pending'   = pending \cup {b}
        /\ avail'     = [ avail EXCEPT ![p][b] =
                             IF BuggyTimeout THEN "missing" ELSE @ ]
        /\ timeouts'  = [ timeouts EXCEPT ![p] = IF @ < UnresponsiveLimit THEN @ + 1 ELSE @ ]
        /\ connected' = [ connected EXCEPT ![p] = @ /\ timeouts[p] + 1 < UnresponsiveLimit ]
        /\ UNCHANGED << verified, retries >>

\* A disconnected peer is redialled (Zebra maintains connections to its
\* initial and discovered peers, redialling them when they fail). Gated by
\* the Redial switch; without it eviction is forever.
Reconnect ==
    \E p \in Peers:
        /\ Redial
        /\ ~connected[p]
        /\ connected' = [ connected EXCEPT ![p] = TRUE ]
        /\ timeouts'  = [ timeouts EXCEPT ![p] = 0 ]
        /\ UNCHANGED << verified, pending, inflight, avail, retries >>

----

Next ==
    \/ Request
    \/ DeliverBlock
    \/ NotFound
    \/ Refused
    \/ Truncated
    \/ Timeout
    \/ Reconnect

\* Strong fairness on the progress actions encodes the real-world assumption
\* that the node keeps trying, a willing peer eventually responds, and the
\* redial loop keeps running. Refused, Truncated and Timeout get no fairness —
\* they are adversarial but never forced.
Spec ==
    Init
    /\ [][Next]_vars
    /\ SF_vars(Request)
    /\ SF_vars(DeliverBlock)
    /\ SF_vars(NotFound)
    /\ SF_vars(Reconnect)

----

\* Liveness: every block is eventually downloaded and verified.
EventuallyAllVerified == <> (verified = Blocks)

----
\* Safety invariants.

TypeOK ==
    /\ verified  \subseteq Blocks
    /\ pending   \subseteq Blocks
    /\ inflight  \in [ Blocks -> Peers \cup {NONE} ]
    /\ avail     \in [ Peers -> [ Blocks -> {"has", "missing", "unknown"} ] ]
    /\ retries   \in [ Blocks -> 0..MaxRetries ]
    /\ timeouts  \in [ Peers -> 0..UnresponsiveLimit ]
    /\ connected \in [ Peers -> BOOLEAN ]

\* The registry never marks a peer missing for a block it actually holds:
\* only the explicit not-found result may mark it. "A refusal, a truncated
\* response, and a timeout are not notfounds."
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
