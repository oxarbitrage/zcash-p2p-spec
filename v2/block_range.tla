---- MODULE block_range ----
(*
get-block-range wire mechanics specification.

The draft's bulk download primitive ("get-block-range") streams a block and
its ancestors in DESCENDING order from an anchor hash, bounded by an exact
count and an exact byte budget: the responder stops before the block that
would push the total past max_bytes — EXCEPT that it MUST be willing to
deliver the first block regardless, or an anchor block larger than the
budget could never be fetched. Over-delivery is a connection error of type
FLOOD ("both bounds are exact, so an honest responder never exceeds them"),
and any truncation — bound reached or voluntary early finish — is
resumable: the next anchor is the hashPrevBlock of the last delivered
block, re-requested from the same or a different peer.

The model: a requester assembles the chain N..1 by repeated anchored
requests against two responders, with adversarially chosen block sizes,
truncation points and responder choice. Blocks are heights; the parent of
h is h-1; the anchor after a delivery of ...,h is h-1.

The requester's FLOOD arithmetic must mirror the responder's stopping rule
exactly. The BuggyFirstInBudget switch makes the requester count the FIRST
block of a response against the byte budget — the natural off-by-one — and
NoHonestFlood is violated: an honest responder delivering an
over-budget anchor block (as the draft requires it to) is disconnected as
a flooder. RangeAssembled and AcceptedIsSuffix verify that the resumption
arithmetic loses nothing and duplicates nothing under every truncation
pattern and peer switch.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxBlock            \* the chain is 1..MaxBlock; the range wanted is all of it
CONSTANT Peers               \* responders; each holds the full chain
CONSTANT MaxCount            \* count limit the requester puts in each request
CONSTANT MaxBytes            \* byte budget the requester puts in each request
CONSTANT Sizes               \* the set block sizes are drawn from
CONSTANT BuggyFirstInBudget  \* TRUE counts the first delivered block against the budget

Blocks == 1..MaxBlock

VARIABLES
    size,     \* [ Blocks -> Sizes ] serialized size of each block (fixed at Init)
    anchor,   \* next height to fetch, descending; 0 = range complete
    accepted, \* heights delivered and accepted
    req,      \* outstanding request: [ active, peer, a ]
    resp,     \* response in flight: [ active, blocks : descending seq of heights ]
    flood     \* TRUE once the requester closed a responder with FLOOD

vars == << size, anchor, accepted, req, resp, flood >>

NoReq  == [ active |-> FALSE, peer |-> "none", a |-> 0 ]
NoResp == [ active |-> FALSE, blocks |-> <<>> ]

SeqSum(s) == LET F[i \in 0..Len(s)] == IF i = 0 THEN 0 ELSE F[i-1] + size[s[i]] IN F[Len(s)]

----

Init ==
    /\ size \in [ Blocks -> Sizes ]
    /\ anchor = MaxBlock
    /\ accepted = {}
    /\ req = NoReq
    /\ resp = NoResp
    /\ flood = FALSE

\* The requester asks any peer for the next span: anchored at its current
\* frontier, with its standard count and byte budget.
SendRequest ==
    \E p \in Peers:
        /\ ~flood
        /\ anchor > 0
        /\ ~req.active /\ ~resp.active
        /\ req' = [ active |-> TRUE, peer |-> p, a |-> anchor ]
        /\ UNCHANGED << size, anchor, accepted, resp, flood >>

\* The responder streams blocks descending from the anchor. It stops at the
\* count bound, before a block (other than the first) that would exceed the
\* byte budget — the first block is delivered regardless — or earlier at
\* will (truncation is resumable). It never over-delivers.
Serve ==
    /\ req.active
    /\ LET a == req.a
           \* the longest prefix the bounds allow
           Fits(k) == /\ k <= MaxCount
                      /\ k <= a          \* the chain ends at height 1
                      /\ \/ k = 1        \* first block: exempt from the budget
                         \/ SeqSum([ i \in 1..k |-> a - i + 1 ]) <= MaxBytes
       IN \E k \in { j \in 1..a : Fits(j) } :
            /\ resp' = [ active |-> TRUE, blocks |-> [ i \in 1..k |-> a - i + 1 ] ]
            /\ req' = NoReq
            /\ UNCHANGED << size, anchor, accepted, flood >>

\* The requester validates the response. The anchor and parent links hold
\* by construction here (heights); the FLOOD arithmetic is the part under
\* test: over-count, or over-budget by a block after the first — or, under
\* the buggy switch, by any block including the first.
RecvResponse ==
    /\ resp.active
    /\ LET bs == resp.blocks
           overCount  == Len(bs) > MaxCount
           overBudget == \E k \in 1..Len(bs) :
                            /\ (k > 1 \/ BuggyFirstInBudget)
                            /\ SeqSum(SubSeq(bs, 1, k)) > MaxBytes
       IN \/ /\ overCount \/ overBudget
             /\ flood' = TRUE
             /\ resp' = NoResp
             /\ UNCHANGED << size, anchor, accepted, req >>
          \/ /\ ~(overCount \/ overBudget)
             /\ accepted' = accepted \cup { bs[i] : i \in 1..Len(bs) }
             /\ anchor' = bs[Len(bs)] - 1
             /\ resp' = NoResp
             /\ UNCHANGED << size, req, flood >>

----

Next == SendRequest \/ Serve \/ RecvResponse

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

\* Liveness: the whole range is eventually assembled.
RangeAssembled == <> (accepted = Blocks)

----
\* Safety invariants.

TypeOK ==
    /\ anchor \in 0..MaxBlock
    /\ accepted \subseteq Blocks
    /\ flood \in BOOLEAN

\* The resumption arithmetic never skips and never repeats: what has been
\* accepted is exactly the suffix of the chain above the current anchor.
AcceptedIsSuffix == accepted = { h \in Blocks : h > anchor }

\* An honest responder, following the draft's exact bounds and the
\* first-block rule, is never closed as a flooder.
NoHonestFlood == ~flood

====
