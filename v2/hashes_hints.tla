---- MODULE hashes_hints ----
(*
get-hashes scheduling-hint verification specification.

get-hashes returns per-block sync-cost metadata — hash, size, txs, txouts,
notes — as scheduling hints. The draft's deferred-penalty rules
("get-hashes", "Misbehavior and Banning"):

  - `txs` and `notes` are determined by the block hash alone, so once the
    block is downloaded a mismatch proves the HINT server lied: SHOULD
    penalize (20 points).
  - `size` is NOT determined by the hash: a block's serialized size
    depends on authorizing data the txid does not commit to. A node that
    got hints from one peer and blocks from another MUST NOT penalize a
    size mismatch unless it has verified the delivered block's authorizing
    data commitment (which binds the serialization via the header);
    "otherwise a peer that pads the blocks it serves would cause the
    penalty to fall on the honest peer that served the hints, which is an
    eviction primitive rather than a defense."

The model: a requester takes hints for one block from a hint server HS and
the block itself from a block server BS. HS may lie about txs or size
(ByzHints); BS may pad the block's serialization without changing its hash
(ByzBlocks). The requester checks hints on download and may verify the
authorizing data commitment afterwards. The PenalizeSizeUnverified switch
is the forbidden reading. PenaltyImpliesLie is the provability principle
at this corner: every penalty lands on a peer that actually lied — and it
is violated exactly when a padding BS frames an honest HS through an
unverified size mismatch, the draft's own eviction-primitive warning
reproduced as a counterexample. LiarEventuallyPenalized checks the
deferred penalty does land on a lying hint server.

Also noted while modeling (feedback item 14): `txouts` is determined by
the block hash exactly as `txs` is, and the draft has the requester rely
on it (the spentness-hint bitmap), yet it appears in neither the
SHOULD-verify sentence nor the penalty table.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT ByzHints                \* the hint server may lie about txs or size
CONSTANT ByzBlocks               \* the block server may pad the serialization
CONSTANT PenalizeSizeUnverified  \* TRUE penalizes a size mismatch before auth verification

TrueTxs  == 2   \* ground truth for the one block modeled
TrueSize == 5
PaddedSize == 7

VARIABLES
    hint_txs,   \* hint received from HS (0 = not yet received)
    hint_size,
    blk_size,   \* serialized size of the delivered block (0 = not yet delivered)
    checked,    \* the on-download hint check has run
    verified,   \* the authorizing data commitment has been checked
    hs_score,   \* penalty assigned to the hint server
    hs_lied     \* ghost: HS actually lied

vars == << hint_txs, hint_size, blk_size, checked, verified, hs_score, hs_lied >>

----

Init ==
    /\ hint_txs = 0 /\ hint_size = 0
    /\ blk_size = 0
    /\ checked = FALSE
    /\ verified = FALSE
    /\ hs_score = 0
    /\ hs_lied = FALSE

\* HS serves the hints; a Byzantine HS may misstate txs or size.
ServeHints ==
    /\ hint_txs = 0
    /\ \E t \in IF ByzHints THEN { TrueTxs, TrueTxs + 1 } ELSE { TrueTxs } :
       \E z \in IF ByzHints THEN { TrueSize, TrueSize + 1 } ELSE { TrueSize } :
            /\ hint_txs' = t
            /\ hint_size' = z
            /\ hs_lied' = (t # TrueTxs \/ z # TrueSize)
    /\ UNCHANGED << blk_size, checked, verified, hs_score >>

\* BS delivers the block. Its transactions are determined by the hash (a
\* different transaction set would not hash to the requested block), so
\* txs is always the truth; the serialization is not, and a Byzantine BS
\* may pad it.
ServeBlock ==
    /\ hint_txs # 0
    /\ blk_size = 0
    /\ \E z \in IF ByzBlocks THEN { TrueSize, PaddedSize } ELSE { TrueSize } :
            blk_size' = z
    /\ UNCHANGED << hint_txs, hint_size, checked, verified, hs_score, hs_lied >>

\* On download, the requester checks the hash-determined hints: a txs
\* mismatch proves the hint server lied. A size mismatch proves nothing
\* yet; penalizing it anyway is the forbidden switch.
CheckOnDownload ==
    /\ blk_size # 0
    /\ ~checked
    /\ checked' = TRUE
    /\ hs_score' = hs_score
                   + (IF hint_txs # TrueTxs THEN 20 ELSE 0)
                   + (IF PenalizeSizeUnverified /\ hint_size # blk_size THEN 20 ELSE 0)
    /\ UNCHANGED << hint_txs, hint_size, blk_size, verified, hs_lied >>

\* The requester verifies the authorizing data commitment: the canonical
\* serialization — and so the true size — is now bound to the hash, and a
\* hint that misstated it is provably the hint server's lie.
VerifyAuthData ==
    /\ blk_size # 0
    /\ checked
    /\ ~verified
    /\ verified' = TRUE
    /\ hs_score' = hs_score + (IF hint_size # TrueSize THEN 20 ELSE 0)
    /\ UNCHANGED << hint_txs, hint_size, blk_size, checked, hs_lied >>

----

Next == ServeHints \/ ServeBlock \/ CheckOnDownload \/ VerifyAuthData

\* Every step of the flow is weakly fair; each fires once.
Spec == Init /\ [][Next]_vars /\ WF_vars(ServeHints) /\ WF_vars(ServeBlock)
             /\ WF_vars(VerifyAuthData) /\ WF_vars(CheckOnDownload)

----

\* Liveness: a lying hint server is eventually penalized (the deferred
\* penalty lands).
LiarEventuallyPenalized == (hs_lied ~> hs_score > 0)

----
\* Safety invariants.

TypeOK ==
    /\ hint_txs \in { 0, TrueTxs, TrueTxs + 1 }
    /\ hint_size \in { 0, TrueSize, TrueSize + 1 }
    /\ blk_size \in { 0, TrueSize, PaddedSize }
    /\ hs_score \in { 0, 20, 40 }

\* The provability principle at this corner: every penalty lands on a peer
\* that actually lied. Violated when a padding block server frames an
\* honest hint server through an unverified size mismatch.
PenaltyImpliesLie == hs_score > 0 => hs_lied

====
