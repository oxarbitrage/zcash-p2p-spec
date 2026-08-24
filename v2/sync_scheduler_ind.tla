---- MODULE sync_scheduler_ind ----
(*
Symbolic verification of the v2 scheduler's safety invariants with
Apalache (https://apalache-mc.org), complementing TLC's exhaustive search.

TLC explores every reachable state at one parameter valuation
(MaxBlock = 2, fixed retry/timeout bounds). Apalache checks the DUAL
projection: bounded depth, but with LagTip, MaxRetries and
UnresponsiveLimit left SYMBOLIC natural numbers — every lag depth, every
retry bound, every unresponsive-peer limit at once. MaxBlock stays
concrete because Apalache does not support integer ranges with symbolic
bounds, and the state is a function over 1..MaxBlock.

Two constant initializers:

  CInitFixed  fixed behaviour (no poisoning, redial on): IndInv =
              ApaTypeOK + RegistryHonest + RegistryHasIsSound +
              VerifiedAreReal.
  CInitAny    ALL behaviour switches symbolic, buggy settings included:
              IndInvAny drops RegistryHonest (the bugs poison "missing"
              entries) but keeps the rest: no switch setting can fabricate
              a "has" entry or a verified block.

Verified locally with Apalache 0.62.1 (results pinned in
../documents/v2-modeling.md; not run in CI — SMT solve times are too
machine-dependent):

  # symbolic base cases (seconds each)
  apalache-mc check --config=sync_scheduler_ind.cfg --cinit=CInitFixed       --init=Init --inv=IndInv --length=0 sync_scheduler_ind.tla
  apalache-mc check --config=sync_scheduler_ind.cfg --cinit=CInitAny       --init=Init --inv=IndInvAny --length=0 sync_scheduler_ind.tla

  # bounded symbolic exploration (about 3 minutes)
  apalache-mc check --config=sync_scheduler_ind.cfg --cinit=CInitFixed       --init=Init --inv=IndInv --length=8 sync_scheduler_ind.tla

With symbolic MaxRetries, runs can be arbitrarily long, so no finite depth
is complete: the bounded result means no violation within 8 steps for any
parameter valuation. A full inductive proof (Inv /\ Next => Inv' from
Gen-arbitrary states — IndInit below) was attempted and is impractical:
the induction step ran over three hours without a verdict at MaxBlock = 4.
The definitions are kept for future Apalache versions.

ApaTypeOK restates TypeOK without function sets over symbolic ranges
(unsupported). This module is Apalache-only: TLC does not run it.
*)
EXTENDS sync_scheduler, Apalache

CInitFixed ==
    /\ LagTip \in Nat
    /\ MaxRetries \in Nat
    /\ UnresponsiveLimit \in Nat /\ UnresponsiveLimit >= 1
    /\ TreatRefusedAsMissing = FALSE
    /\ TreatTruncatedAsMissing = FALSE
    /\ BuggyTimeout = FALSE
    /\ Redial = TRUE

CInitAny ==
    /\ LagTip \in Nat
    /\ MaxRetries \in Nat
    /\ UnresponsiveLimit \in Nat /\ UnresponsiveLimit >= 1
    /\ TreatRefusedAsMissing \in BOOLEAN
    /\ TreatTruncatedAsMissing \in BOOLEAN
    /\ BuggyTimeout \in BOOLEAN
    /\ Redial \in BOOLEAN

\* TypeOK, restated without function sets over symbolic integer ranges.
ApaTypeOK ==
    /\ verified \subseteq Blocks
    /\ pending \subseteq Blocks
    /\ DOMAIN inflight = Blocks
    /\ \A b \in Blocks : inflight[b] \in Peers \cup { NONE }
    /\ DOMAIN avail = Peers
    /\ \A p \in Peers :
        /\ DOMAIN avail[p] = Blocks
        /\ \A b \in Blocks : avail[p][b] \in { "has", "missing", "unknown" }
    /\ DOMAIN retries = Blocks
    /\ \A b \in Blocks : retries[b] >= 0 /\ retries[b] <= MaxRetries
    /\ DOMAIN timeouts = Peers
    /\ \A p \in Peers : timeouts[p] >= 0 /\ timeouts[p] <= UnresponsiveLimit
    /\ DOMAIN connected = Peers
    /\ \A p \in Peers : connected[p] \in BOOLEAN

\* Inductive for the fixed behaviour, for any LagTip / MaxRetries /
\* UnresponsiveLimit.
IndInv ==
    /\ ApaTypeOK
    /\ RegistryHonest
    /\ RegistryHasIsSound
    /\ VerifiedAreReal

\* Inductive under EVERY switch setting, buggy ones included.
IndInvAny ==
    /\ ApaTypeOK
    /\ RegistryHasIsSound
    /\ VerifiedAreReal

\* Arbitrary typed states for the induction step (the Gen bound covers the
\* set and function sizes; IndInv constrains the rest).
GenState ==
    /\ verified = Gen(6)
    /\ pending = Gen(6)
    /\ inflight = Gen(6)
    /\ avail = Gen(16)
    /\ retries = Gen(6)
    /\ timeouts = Gen(4)
    /\ connected = Gen(4)

IndInit    == GenState /\ IndInv
IndInitAny == GenState /\ IndInvAny

====
