---- MODULE compact_relay ----
(*
Compact block relay reconstruction specification.

Models the draft's "Compact Block Relay" machinery between a sender S (who
has the new block) and a requester R (who holds some of its transactions):
compact block announcements carrying a per-announcement nonce, short-ID
matching against R's mempool, `get-tx` SHORTID requests for the missing
transactions, and the reconstruction outcome.

The stateful subtlety is the nonce: short transaction IDs are relative to
one compact block's nonce, and the responding node interprets SHORTID
references "using the nonce of the compact block it most recently sent to
the requesting peer for the identified block" ("Requesting Missing
Transactions"). A sender may legitimately announce the same block more than
once with a fresh nonce — for example when re-announcing its tip on a
replacement announcement stream (see Finding 2 in
../documents/v2-modeling.md). SHORTID requests computed from an earlier
announcement then arrive under a newer nonce: each reference matches no
transaction (not-found) or, by 48-bit collision, a wrong one. The model
resolves that choice adversarially.

Announcements are best-effort: under backpressure the sender may drop one
rather than queue it ("Announcement Streams"), and a reset replacement
stream loses records in flight. The model lets a re-announcement be lost
while the requester is mid-attempt — after which every reference the
requester can ever send is stale, and the compact path alone cannot
converge.

The draft's escape hatch is reconstruction failure handling: the node
"SHOULD fall back to requesting the full block via get-blocks, and MUST NOT
assign a misbehavior penalty solely because reconstruction failed". Two
switches probe it:

  Fallback           = FALSE -> reconstruction failure retries the compact
                                path instead of falling back. Liveness
                                (EventuallyHasBlock) is violated: announce
                                budgets end and the requester waits forever.
                                The SHOULD is load-bearing — no other rule
                                guarantees the block arrives.
  PenalizeReconFail  = TRUE  -> reconstruction failure scores 20 points,
                                against the MUST NOT. NoHonestPenalty is
                                violated: honest nonce churn frames the
                                sender.

With Fallback = TRUE and no penalties, every property holds under maximal
nonce churn, and WrongTxNeverAccepted states the draft's own claim that
short-ID matching cannot weaken consensus: a wrongly matched transaction
fails the merkle check and never enters an accepted block.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NTx                 \* transactions in the block: 1..NTx
CONSTANT MaxAnnounce         \* compact block announcements available to S
CONSTANT Fallback            \* see module comment
CONSTANT PenalizeReconFail   \* see module comment

Txs == 1..NTx

VARIABLES
    mempool,    \* R: subset of Txs held before the block arrives
    has_block,  \* R: TRUE once the block is accepted (fully reconstructed or fetched)
    score,      \* R's misbehavior score for S (MUST stay 0)
    ann_q,      \* announcement stream toward R: sequence of nonces (in order)
    last_sent,  \* S: nonce of the compact block most recently sent to R (0 = none)
    announced,  \* S: announcements used
    via,        \* how R got the block: "none" | "match" | "recon" | "full" (ghost)
    req,        \* SHORTID get-tx toward S: [ active, nonce, missing ]
    resp,       \* get-tx response toward R: [ active, ok : txs served correctly,
                \*                             bad : a not-found or wrong tx occurred ]
    fb          \* fallback get-blocks state: "none" | "requested" | "served"

vars == << mempool, has_block, score, ann_q, last_sent, announced, via, req, resp, fb >>

NoReq  == [ active |-> FALSE, nonce |-> 0, missing |-> {} ]
NoResp == [ active |-> FALSE, ok |-> {}, bad |-> FALSE ]

----

Init ==
    /\ mempool \in SUBSET Txs
    /\ has_block = FALSE
    /\ score = 0
    /\ ann_q = <<>>
    /\ via = "none"
    /\ last_sent = 0
    /\ announced = 0
    /\ req = NoReq
    /\ resp = NoResp
    /\ fb = "none"

\* S announces the block as a compact block with a fresh nonce — the first
\* announcement, or a legitimate re-announcement (replacement stream,
\* BIP 152 high-bandwidth relay). Nonces are the announcement number.
Announce ==
    /\ announced < MaxAnnounce
    /\ announced' = announced + 1
    /\ ann_q' = Append(ann_q, announced + 1)
    /\ last_sent' = announced + 1
    /\ UNCHANGED << mempool, has_block, score, via, req, resp, fb >>

\* R processes the next compact block announcement: transactions it holds
\* match by short ID; the missing ones are requested by SHORTID reference,
\* remembering which nonce they were computed under. If nothing is missing
\* the block is reconstructed immediately. Announcements for a block already
\* held are ignored.
RecvCompactBlock ==
    /\ ann_q # <<>>
    /\ ~req.active /\ ~resp.active /\ fb = "none"
    /\ ann_q' = Tail(ann_q)
    /\ IF has_block
       THEN UNCHANGED << mempool, has_block, score, last_sent, announced, via, req, resp, fb >>
       ELSE IF Txs \subseteq mempool
       THEN /\ has_block' = TRUE
            /\ via' = "match"
            /\ UNCHANGED << mempool, score, last_sent, announced, req, resp, fb >>
       ELSE /\ req' = [ active |-> TRUE, nonce |-> Head(ann_q), missing |-> Txs \ mempool ]
            /\ UNCHANGED << mempool, has_block, score, last_sent, announced, via, resp, fb >>

\* A queued re-announcement is lost while the requester is busy with an
\* attempt: announcements are best-effort under backpressure, and a reset
\* replacement stream drops records in flight. Adversarial, never forced.
DropAnnouncement ==
    /\ ann_q # <<>>
    /\ req.active \/ resp.active
    /\ ann_q' = Tail(ann_q)
    /\ UNCHANGED << mempool, has_block, score, last_sent, announced, via, req, resp, fb >>

\* S serves the SHORTID references, interpreting them under the nonce of the
\* compact block it most recently sent. Fresh references resolve exactly;
\* stale ones (an announcement has happened since) match no transaction or,
\* by collision, a wrong one — resolved adversarially per reference.
ServeGetTx ==
    /\ req.active
    /\ \E badset \in SUBSET req.missing :
         /\ (req.nonce = last_sent) => badset = {}
         /\ (req.nonce # last_sent) => badset # {}
         /\ resp' = [ active |-> TRUE, ok |-> req.missing \ badset, bad |-> badset # {} ]
    /\ req' = NoReq
    /\ UNCHANGED << mempool, has_block, score, ann_q, last_sent, announced, via, fb >>

\* R completes reconstruction from a clean response: the block passes its
\* merkle check and is accepted.
RecvTxsComplete ==
    /\ resp.active
    /\ ~resp.bad
    /\ mempool' = mempool \cup resp.ok
    /\ has_block' = TRUE
    /\ via' = "recon"
    /\ resp' = NoResp
    /\ UNCHANGED << score, ann_q, last_sent, announced, req, fb >>

\* A not-found result or a wrong transaction makes reconstruction fail (a
\* wrong transaction fails the merkle check). What happens next is the
\* switch: fall back to get-blocks as the draft says SHOULD, or retry the
\* compact path with the next announcement; and, forbidden by the draft's
\* MUST NOT, a penalty may be scored.
RecvTxsFailed ==
    /\ resp.active
    /\ resp.bad
    /\ mempool' = mempool \cup resp.ok
    /\ resp' = NoResp
    /\ fb' = IF Fallback THEN "requested" ELSE "none"
    /\ score' = IF PenalizeReconFail THEN score + 20 ELSE score
    /\ UNCHANGED << has_block, ann_q, last_sent, announced, via, req >>

\* The fallback get-blocks round trip: S always holds the full block.
ServeFallback ==
    /\ fb = "requested"
    /\ fb' = "served"
    /\ UNCHANGED << mempool, has_block, score, ann_q, last_sent, announced, via, req, resp >>

RecvFallback ==
    /\ fb = "served"
    /\ has_block' = TRUE
    /\ via' = "full"
    /\ fb' = "none"
    /\ UNCHANGED << mempool, score, ann_q, last_sent, announced, req, resp >>

----

Next ==
    \/ Announce
    \/ RecvCompactBlock
    \/ DropAnnouncement
    \/ ServeGetTx
    \/ RecvTxsComplete
    \/ RecvTxsFailed
    \/ ServeFallback
    \/ RecvFallback

\* Everything a peer must eventually do is weakly fair; Announce is fair
\* too, so the block is announced at all, and its budget bounds the churn.
\* DropAnnouncement carries no fairness: it is adversarial, never forced —
\* WF on the other actions cannot force it either, since RecvCompactBlock
\* is enabled whenever it is.
Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Announce)
    /\ WF_vars(RecvCompactBlock)
    /\ WF_vars(ServeGetTx)
    /\ WF_vars(RecvTxsComplete)
    /\ WF_vars(RecvTxsFailed)
    /\ WF_vars(ServeFallback)
    /\ WF_vars(RecvFallback)

----

\* Liveness: R eventually holds the block.
EventuallyHasBlock == <> has_block

----
\* Safety invariants.

TypeOK ==
    /\ mempool \subseteq Txs
    /\ has_block \in BOOLEAN
    /\ score \in Nat
    /\ last_sent \in 0..MaxAnnounce
    /\ announced \in 0..MaxAnnounce
    /\ fb \in { "none", "requested", "served" }
    /\ via \in { "none", "match", "recon", "full" }

\* The draft's MUST NOT: reconstruction failure carries no penalty.
NoHonestPenalty == score = 0

\* The draft's consensus claim: short-ID matching cannot weaken consensus.
\* A block accepted through reconstruction was assembled from the full,
\* correct transaction set (bad responses never reach the mempool and fail
\* the merkle check instead); anything else arrived as a full block.
WrongTxNeverAccepted ==
    has_block /\ via \in { "match", "recon" } => Txs \subseteq mempool

====
