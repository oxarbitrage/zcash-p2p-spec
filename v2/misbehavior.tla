---- MODULE misbehavior ----
(*
Version 2 misbehavior and banning specification.

Models the receiving side of the draft's "Misbehavior and Banning" section:
a local node scoring the peers it is connected to. The draft constrains
every penalty by a provability principle — a node MUST NOT penalize
behaviour that a conformant peer acting on honest but divergent state could
produce — and motivates it: penalties on weaker evidence let an attacker
induce honest nodes to ban one another. This module turns that sentence and
its converse into checkable properties.

Remote peers are honest or Byzantine. Honest peers may legitimately send:

    divergent headers    contiguous, valid proof of work, but not connecting
                         to the local chain: the peer follows another fork
                         ("Block Announcements", "Headers-First
                         Synchronization" — MUST NOT penalize).
    requested invalid    a block the local node itself requested by hash
                         whose content fails consensus validation: the
                         responder served exactly the bytes the hash names;
                         blame lies with the announcer ("Misbehavior and
                         Banning", exemption "Content of requested objects").

Byzantine peers additionally send provable violations from the penalty
table: oversize get-headers responses (+20), non-contiguous headers (+20),
and an announced block with invalid proof of work (+100).

Three booleans select wrong readings of the draft:

  PenalizeNonConnecting    = TRUE -> divergent headers score 20 points
  PenalizeRequestedInvalid = TRUE -> a requested invalid block scores 100
  PerConnectionScore       = TRUE -> the score is per connection, reset on
                                     reconnect, instead of keyed by address

Under the first two, NoHonestBan is violated: an honest peer on another fork
is banned. Under the third, PersistentAttackerBanned is violated: a
Byzantine peer sheds its score by reconnecting before the threshold —
the draft's stated reason for address-keyed persistent scores.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT Peers                     \* remote peers of the local node
CONSTANT Byzantine                 \* subset of Peers sending provable violations
CONSTANT BanThreshold              \* score at which a peer is disconnected and banned
CONSTANT PenalizeNonConnecting     \* TRUE penalizes divergent headers (buggy)
CONSTANT PenalizeRequestedInvalid  \* TRUE penalizes requested invalid blocks (buggy)
CONSTANT PerConnectionScore        \* TRUE resets the score on reconnect (buggy)

Honest == Peers \ Byzantine

VARIABLES
    score,      \* [ Peers -> 0..BanThreshold ] misbehavior score, capped
    banned,     \* [ Peers -> BOOLEAN ] banned addresses (absorbing)
    connected   \* [ Peers -> BOOLEAN ] currently connected

vars == << score, banned, connected >>

Min(a, b) == IF a < b THEN a ELSE b

----

Init ==
    /\ score     = [ p \in Peers |-> 0 ]
    /\ banned    = [ p \in Peers |-> FALSE ]
    /\ connected = [ p \in Peers |-> TRUE ]

\* The local node adds pts to p's score; at the threshold it closes the
\* connection with MISBEHAVIOR and bans the address ("Misbehavior and
\* Banning": score thresholds and banning).
Penalize(p, pts) ==
    LET s == Min(score[p] + pts, BanThreshold)
    IN /\ score'     = [ score EXCEPT ![p] = s ]
       /\ banned'    = [ banned EXCEPT ![p] = s >= BanThreshold ]
       /\ connected' = [ connected EXCEPT ![p] = @ /\ s < BanThreshold ]

NoPenalty == UNCHANGED << score, banned, connected >>

----

\* An honest peer on a divergent fork answers get-headers, or announces a
\* header, that does not connect to the local chain. The draft forbids a
\* penalty; PenalizeNonConnecting scores it anyway.
HonestDivergentHeaders ==
    \E p \in Honest:
        /\ connected[p]
        /\ IF PenalizeNonConnecting THEN Penalize(p, 20) ELSE NoPenalty

\* An honest peer serves a block the local node requested by hash whose
\* content fails consensus validation — exactly the bytes the hash names
\* (for example an artifact held for checkpointed sync). The draft exempts
\* it; PenalizeRequestedInvalid scores it anyway.
HonestRequestedInvalid ==
    \E p \in Honest:
        /\ connected[p]
        /\ IF PenalizeRequestedInvalid THEN Penalize(p, 100) ELSE NoPenalty

\* Provable violations from the penalty table: only Byzantine peers produce
\* them, and they always score.
ByzOversizeHeaders ==
    \E p \in Byzantine: connected[p] /\ Penalize(p, 20)

ByzNonContiguousHeaders ==
    \E p \in Byzantine: connected[p] /\ Penalize(p, 20)

ByzInvalidPowBlock ==
    \E p \in Byzantine: connected[p] /\ Penalize(p, 100)

\* A peer may disconnect at will — in particular a Byzantine peer trying to
\* shed its score.
Disconnect ==
    \E p \in Peers:
        /\ connected[p]
        /\ connected' = [ connected EXCEPT ![p] = FALSE ]
        /\ UNCHANGED << score, banned >>

\* A disconnected, unbanned peer of S reconnects. Whether its score survives
\* the new connection is the PerConnectionScore switch; the draft wants
\* scores keyed by address precisely so that reconnecting sheds nothing.
ReconnectFrom(S) ==
    \E p \in S:
        /\ ~connected[p]
        /\ ~banned[p]
        /\ connected' = [ connected EXCEPT ![p] = TRUE ]
        /\ score'     = [ score EXCEPT ![p] = IF PerConnectionScore THEN 0 ELSE @ ]
        /\ UNCHANGED << banned >>

Reconnect == ReconnectFrom(Peers)

----

Next ==
    \/ HonestDivergentHeaders
    \/ HonestRequestedInvalid
    \/ ByzOversizeHeaders
    \/ ByzNonContiguousHeaders
    \/ ByzInvalidPowBlock
    \/ Disconnect
    \/ Reconnect

\* Fairness encodes the hypothesis of PersistentAttackerBanned: a Byzantine
\* peer that KEEPS misbehaving — and keeps reconnecting when disconnected —
\* is the one that must end up banned. Fairness is on the Byzantine peer's
\* own reconnection (an honest peer reconnecting must not discharge it);
\* honest events and Disconnect are never forced. The configurations use a
\* single Byzantine peer, so the existential fairness cannot starve one
\* attacker in favour of another.
Spec ==
    Init
    /\ [][Next]_vars
    /\ SF_vars(ByzOversizeHeaders)
    /\ SF_vars(ReconnectFrom(Byzantine))

----

\* Liveness: a persistently misbehaving Byzantine peer is eventually banned.
\* Violated under PerConnectionScore: reconnecting before the threshold
\* sheds the score forever.
PersistentAttackerBanned == <> \A p \in Byzantine : banned[p]

----
\* Safety invariants.

TypeOK ==
    /\ score     \in [ Peers -> 0..BanThreshold ]
    /\ banned    \in [ Peers -> BOOLEAN ]
    /\ connected \in [ Peers -> BOOLEAN ]

\* The provability principle, as an outcome: no honest peer is ever banned,
\* however divergent its chain view. Violated under either buggy penalty.
NoHonestBan ==
    \A p \in Honest : ~banned[p] /\ score[p] < BanThreshold

\* A banned peer is disconnected and stays banned.
BanIsFinal ==
    \A p \in Peers : banned[p] => ~connected[p]

====
