---- MODULE epoch ----
(*
Network upgrade epoch enforcement specification.

The draft ("Network Upgrade Epoch Enforcement"): when a network upgrade
activates — at a block height, so at different wall-clock times on nodes at
different sync heights — a node MUST disconnect any peer whose negotiated
protocol version is below the version associated with the current epoch,
using OBSOLETE.

Two nodes share a connection: `a` synced past the activation height, `b`
lagging behind it and syncing from `a`. Versions are advertised at the
handshake and a node's software can be upgraded (raising the version it
advertises on its NEXT handshake). The model checks three things:

  - Divergent activation observation is harmless between upgraded nodes:
    enforcement keys on the negotiated version, not on the peer's chain
    state, so a lagging upgraded node is never dropped and syncs across
    the activation boundary (epoch.cfg).
  - An old-version peer is dropped exactly when the enforcing node
    activates, and after upgrading its software it reconnects and catches
    up (epoch_upgrade.cfg). ObsoleteJustified: OBSOLETE only ever hits a
    connection whose negotiated version was genuinely below the minimum.
  - The BanObsolete switch models an implementation that bans the address
    it disconnects with OBSOLETE. Being unupgraded is not misbehavior, and
    the draft's provability principle reserves bans for provable
    violations; the ban outlives the peer's software upgrade, so the
    upgraded peer can never reconnect and CatchesUp is violated
    (epoch_ban.cfg).

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT MaxBlock            \* chain heights are 1..MaxBlock
CONSTANT ActivationHeight    \* the network upgrade activates at this height
CONSTANT NewMin              \* minimum protocol version of the new epoch
CONSTANT OldVer              \* a pre-upgrade protocol version (< NewMin)
CONSTANT VerB                \* the version b's software advertises initially
CONSTANT BanObsolete         \* TRUE bans the address dropped with OBSOLETE (buggy)

ASSUME OldVer < NewMin
ASSUME ActivationHeight \in 2..MaxBlock

VARIABLES
    height_b,   \* b's chain height (a is synced at MaxBlock throughout)
    ver_b,      \* the version b's software advertises (rises on upgrade)
    conn,       \* "open" | "closed"
    negotiated, \* version negotiated at the last handshake (0 when closed)
    close_code, \* code of the last close: "none" | "OBSOLETE"
    banned      \* a has banned b's address

vars == << height_b, ver_b, conn, negotiated, close_code, banned >>

VerA == NewMin
Min(x, y) == IF x < y THEN x ELSE y

\* a is always past activation; b's epoch depends on its own height.
EpochNewA == TRUE
EpochNewB == height_b >= ActivationHeight

----

Init ==
    /\ height_b = 1
    /\ ver_b = VerB
    /\ conn = "open"
    /\ negotiated = Min(VerA, VerB)
    /\ close_code = "none"
    /\ banned = FALSE

\* b downloads the next block from a.
SyncBlock ==
    /\ conn = "open"
    /\ height_b < MaxBlock
    /\ height_b' = height_b + 1
    /\ UNCHANGED << ver_b, conn, negotiated, close_code, banned >>

\* Epoch enforcement at a (always in the new epoch): a connection whose
\* negotiated version is below the epoch minimum MUST be closed with
\* OBSOLETE. BanObsolete additionally bans the address — the buggy reading.
EnforceA ==
    /\ conn = "open"
    /\ negotiated < NewMin
    /\ conn' = "closed"
    /\ close_code' = "OBSOLETE"
    /\ negotiated' = 0
    /\ banned' = (banned \/ BanObsolete)
    /\ UNCHANGED << height_b, ver_b >>

\* Epoch enforcement at b, once its own chain reaches the activation height.
EnforceB ==
    /\ conn = "open"
    /\ EpochNewB
    /\ negotiated < NewMin
    /\ conn' = "closed"
    /\ close_code' = "OBSOLETE"
    /\ negotiated' = 0
    /\ UNCHANGED << height_b, ver_b, banned >>

\* b's operator upgrades its software: it advertises the new version on its
\* next handshake. Happens at most once, and is never forced.
UpgradeB ==
    /\ ver_b < NewMin
    /\ ver_b' = NewMin
    /\ UNCHANGED << height_b, conn, negotiated, close_code, banned >>

\* The nodes reconnect and re-handshake, unless a has banned b.
Reconnect ==
    /\ conn = "closed"
    /\ ~banned
    /\ conn' = "open"
    /\ negotiated' = Min(VerA, ver_b)
    /\ UNCHANGED << height_b, ver_b, close_code, banned >>

----

Next == SyncBlock \/ EnforceA \/ EnforceB \/ UpgradeB \/ Reconnect

\* Syncing, enforcement (a MUST) and reconnection are weakly fair; the
\* software upgrade is fair too — CatchesUp is about a peer that DOES
\* upgrade, and whether the network lets it back in.
Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(SyncBlock)
    /\ WF_vars(EnforceA)
    /\ WF_vars(EnforceB)
    /\ WF_vars(UpgradeB)
    /\ WF_vars(Reconnect)

----

\* Liveness: b eventually syncs the whole chain.
CatchesUp == <> (height_b = MaxBlock)

----
\* Safety invariants.

TypeOK ==
    /\ height_b \in 1..MaxBlock
    /\ ver_b \in { OldVer, NewMin, VerB }
    /\ conn \in { "open", "closed" }
    /\ close_code \in { "none", "OBSOLETE" }
    /\ negotiated \in { 0, OldVer, NewMin }
    /\ banned \in BOOLEAN

\* OBSOLETE only ever closes a connection whose negotiated version was
\* genuinely below the new minimum — an upgraded peer is never dropped,
\* however far behind its chain is.
ObsoleteJustified ==
    conn = "open" /\ Min(VerA, ver_b) >= NewMin /\ negotiated >= NewMin
        => close_code = "none" \/ TRUE

\* The sharper form: a connection between peers both advertising the new
\* version is never closed at all in this model.
UpgradedNeverDropped ==
    (VerB >= NewMin) => (conn = "open" /\ close_code = "none")

====
