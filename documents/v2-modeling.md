# Modeling the version 2 P2P protocol (draft ZIP)

Draft under model: *Version 2 Zcash P2P Network Protocol*,
[zcash/zips#1344](https://github.com/zcash/zips/pull/1344), file
`zips/draft-arya-jvff-p2p-quic-transport.md`, pinned at revision **`a3f4fa2a`**
(the revision Zebra's `SPEC-CONFORMANCE.md` is written against). The draft is
still moving; section names below refer to that revision. The draft's
`# Formal Model` section cites this repository and notes that the model had
not yet been updated for the new protocol — this document describes that
update, phase by phase.

All four phases plus the simultaneous-dial, get-mempool, Byzantine,
compact-block and epoch addenda are complete; this document describes them. Reference
implementation consulted: Zebra's five-PR draft stack
[#11273](https://github.com/ZcashFoundation/zebra/pull/11273) –
[#11277](https://github.com/ZcashFoundation/zebra/pull/11277)
(`zebra-network/src/peer/v2/connection.rs` on branch
`p2p-v2-5-peer-set-integration`).

## Why a new model rather than an edit

The legacy model (`protocol.tla`) is built around one ordered FIFO per
connection: a TCP byte pipe carrying framed messages. That is the one thing
the v2 protocol does not have. QUIC gives a connection *many* streams, each
ordered on its own, with the explicit guarantee that streams are mutually
independent ("Transport Requirements"). Every rule in the draft that says
"one X at a time" or "before Y" is therefore a rule about events that may be
observed in a different order than they were produced. The legacy model
cannot express that, so the v2 model lives in its own directory (`v2/`)
with its own stream layer; the legacy model is left untouched as the formal
companion of ZIP-204.

## Phase 1 — stream layer, handshake, announcement streams

### The abstraction

| Draft concept | Model |
|---|---|
| Connection | `nodes[n].conn[m]` ∈ `none / initiator / responder / closed`; establishment is atomic (the QUIC handshake is out of scope) |
| Stream | a slot `<<opener, k>>` per connection, `k ∈ 1..MaxStreams`; freed when both peers have closed it |
| Stream type byte | first element of the stream's queue; the receiver learns the type only by consuming it |
| Data in flight toward n | `nodes[n].streams[m][sid].inq`, one FIFO **per stream** — delivery picks any stream, so cross-stream reordering is free |
| FIN | queue sentinel (ordered after the data it follows) |
| RESET_STREAM / STOP_SENDING | flags on the receiver's record, observable regardless of queued data (they overtake data in QUIC) |
| init record | `MakeInit(version, start_height)`; other fields constant |
| Handshake complete | `init_sent ∧ init_recvd`, per side ("Handshake Sequence", step 3) |
| Negotiated version | `min(local, remote)` |
| Announcement stream | a unidirectional stream of type `0x10`; sender keeps at most one live per type |
| Header announcement | `MakeHeaderAnnouncement(height)` |
| New blocks | `MineBlock`, bounded by `MaxBlock`, gives peers something to announce |
| Sender-initiated finish/reset of an announcement stream | `FinishAnnouncementStream` / `ResetAnnouncementStream`, bounded by `MaxRestarts`, never forced |

Two constants select how a receiver reads the draft:

- `StrictSingleton` — TRUE: a second open announcement stream of the same
  type from a peer is a `PROTOCOL_ERROR` (the literal text of "Announcement
  Streams"). FALSE: the receiver accepts the new stream and drains both.
- `RefusePreHandshake` — TRUE: announcement streams arriving before the
  local handshake is complete are refused with `REFUSED` ("Connection
  Handshake": a node MAY refuse them). FALSE: they wait until it completes.

Actions follow the legacy model's discipline: a peer acts only on its own
records. The transport is the only thing that writes both peers' records at
once (connection open/close, stream open, freeing a slot once both sides
closed it).

### What is checked

Safety (all configurations):

| Invariant | Draft rule |
|---|---|
| `OneHandshakeStream` | exactly one handshake stream, opened by the initiator |
| `HandshakeBeforeStreams` | no stream before sending `init`; no announcement stream before the handshake completes |
| `NegotiatedVersionIsMin` | negotiated version is the minimum of the advertised versions |
| `SenderSingleton` | a sender never has two live announcement streams of one type toward a peer |
| `CloseJustified` | `OBSOLETE` is only used against a peer that advertised a version below the minimum |
| `NoHonestProtocolError` | with no adversarial actions in the model, no close other than `OBSOLETE` ever happens |
| `TypeOK`, `SlotsConsistent` | model sanity |

Liveness (2-peer configurations): `HandshakeCompletes` and
`AnnouncementsFlow` (every peer eventually learns every peer's final tip).

### Results

State counts in this table are from the Phase 1 constants (`MaxStreams = 3`,
`MaxBlock = 2`, `MaxRestarts = 1`); the configurations were retuned in Phase 2,
see below.

| Config | Reading | Expected | Result (2 peers, complete) |
|---|---|---|---|
| `protocol.cfg` | tolerant receiver | all pass | 177,564 states, passes |
| `protocol_refuse.cfg` | refuse pre-handshake streams | all pass | 334,164 states, passes |
| `protocol_obsolete.cfg` | one peer may be below `MinVersion` | all pass (`OBSOLETE` is sanctioned) | 178,906 states, passes |
| `protocol_strict.cfg` | strict singleton | `NoHonestProtocolError` **violated** | 12-state counterexample |
| `protocol_3peers.cfg` | tolerant, symmetry | bounded, no error | no error within the time bound |

```bash
cd v2
java -jar ../tla2tools.jar -config protocol.cfg          protocol.tla   # passes
java -jar ../tla2tools.jar -config protocol_refuse.cfg   protocol.tla   # passes
java -jar ../tla2tools.jar -config protocol_obsolete.cfg protocol.tla   # passes
java -jar ../tla2tools.jar -config protocol_strict.cfg   protocol.tla   # NoHonestProtocolError violated
```

### Finding 1 — announcement stream replacement race (strict reading)

The counterexample, narrated (peer1 is the initiator):

1. Connect; peer1 opens the handshake stream and sends `init`; peer2 reads
   the type byte, sends its `init`; both consume the other's `init`. Both
   handshakes complete.
2. peer1 opens announcement stream **A** (slot 2). peer2 reads A's type
   byte: one open `0x10` stream from peer1.
3. peer1 finishes A — allowed; the draft says a sender that finishes or
   resets an announcement stream MAY open a replacement. A's FIN is now
   queued on A.
4. peer1 opens replacement **B** (slot 3).
5. Streams are independent, so peer2 consumes B's type byte before A's
   FIN. peer2 now sees two open `0x10` streams from peer1 and, under the
   strict reading, closes the connection with `PROTOCOL_ERROR`.

Every step is a MAY/SHOULD-sanctioned action of a conformant peer. The same
trace exists with a reset instead of a finish (the reset flag can be
observed even later than a FIN because it is not ordered with the data).

The receiver cannot, in principle, tell this interleaving from a peer that
really opened two concurrent streams: the only difference is a FIN it has
not yet read. So the strict rule has no enforcement value against a
misbehaving peer (stream concurrency limits already bound the damage) while
it does disconnect honest ones.

**Zebra.** `read_inbound_announcement_stream` implements the strict reading:
it inserts the type byte into `open_inbound_announcements` when it reads it
and calls `fail_protocol` if the type is already present; the entry is
removed only when the old stream's read loop ends. Zebra's *sender*
(`write_announcements`) only opens a replacement after a write error, i.e.
after the receiver itself stopped the stream — in which case the receiver has
already removed the entry, so Zebra↔Zebra never trips the check. Any
implementation that rotates or resets its own announcement streams (which the
draft permits) would be disconnected by a Zebra peer.

Verdict: a spec-level ambiguity with a concrete interoperability hazard, not
an implementation bug. Proposed wording is in
[`v2-spec-feedback.md`](v2-spec-feedback.md).

### Observation 2 — re-announce after a reset

Before the sender was made to re-announce its tip on a replacement stream,
`AnnouncementsFlow` failed in the tolerant configuration: a block announced
on a stream that the sender then *reset* is lost (the reset overtakes the
record), and the replacement carried nothing. The draft calls announcements
best-effort and the peer would recover through a later `get-headers`, so this
is not a protocol error — but it is worth a sentence in the draft:
*a sender that resets an announcement stream SHOULD re-announce its current
tip on the replacement.* The model now does this in
`OpenAnnouncementStream`.

### Non-finding — refusing streams before the handshake completes

Stream independence also lets a peer's first announcement stream arrive
before its `init` record has been read locally. Under `RefusePreHandshake`
the receiver refuses it with `REFUSED`, the sender resets and reopens, and
the loop ends as soon as the receiver processes the `init` (fairness on
`RecvInit`). No property fails: the draft's MAY-refuse / MAY-buffer choice is
safe either way. The refuse path is exercised (`RecvStop` fires in ~16k
states per TLC coverage).

### State space notes

- Closed streams collapse to one canonical record and slots are reused once
  both sides closed, so finish/reopen cycles do not grow the state.
- Fairness is `WF_vars(Next)` plus `WF_vars(RecvInit)`. Mining and
  sender-initiated restarts are bounded, so every behaviour quiesces and
  weak fairness on `Next` already forces every enabled receive; the one
  unbounded loop (refuse/reopen) is ended by fairness on `RecvInit`. Per-action
  strong fairness was tried first and made TLC's liveness check an order of
  magnitude slower for no gain.
- `MaxStreams = 3` is the minimum that exhibits Finding 1 (handshake stream
  plus old and new announcement stream for the initiator).

## Phase 2 — request streams and headers-first synchronization

### The abstraction

| Draft concept | Model |
|---|---|
| Request stream | bidirectional stream of type `0x01` (`get-headers`) or `0x02` (`get-blocks`); the requester writes the request record and its FIN in one step (`RequesterStream`) |
| Response | one record (`headers` / `blocks`) followed by FIN; the responder may serve as soon as the request record is consumed, before the requester's FIN |
| Both directions done | new stream field `in_done`; a bidirectional stream collapses to `ClosedStream` only once the local sending direction is finished/reset **and** the peer's FIN has been consumed |
| Block locator | the requester's height (single linear chain) |
| `get-headers` response | heights `loc+1 .. min(loc+MaxHeaders, tip)`; `count = 0` is legal |
| `get-blocks` early finish | the responder nondeterministically delivers any non-empty prefix of the held blocks and finishes ("MAY finish after any complete entry") |
| Sync driver | `peer_tip > height ∧ want = <<>> ∧ no open request → get-headers`; `want ≠ <<>> → get-blocks` for the next `MaxBlocksPerRequest`; one request outstanding per peer |
| Oversize / non-contiguous headers | discarded, `score += 20` (the draft's override of the generic connection-error rule) |
| Chain growth | only the peer at the highest height mines (`MineBlock`), so there is one chain everyone catches up with |

### What is checked

New invariants: `BlocksContiguous`, `RequestsAfterHandshake` (requests only
after the handshake, one at a time per peer), `ResponsesBounded`
(≤ `MaxHeaders` contiguous headers, ≤ `MaxBlocksPerRequest` hashes),
`NoHonestPenalty` (score stays 0). New liveness: `EventualConsensus`.

### Results

| Config | Focus | Result |
|---|---|---|
| `protocol.cfg` | 3-block chain, `MaxHeaders = 2`, `MaxBlocksPerRequest = 2`, no restarts | 332,871 states, all invariants + `HandshakeCompletes`, `AnnouncementsFlow`, `EventualConsensus` pass |
| `protocol_restart.cfg` | 2-block chain, one finish/reset per direction, `MaxStreams = 3` | 1,402,498 states, passes |
| `protocol_refuse.cfg` | refuse pre-handshake streams (requests included) | 31,550 states, passes |
| `protocol_obsolete.cfg` | `OBSOLETE` path (no `EventualConsensus`: the only connection closes) | 14,654 states, passes |
| `protocol_strict.cfg` | strict singleton | still the 12-state violation |

The draft's small constants are replaced by `MaxHeaders = 2` and
`MaxBlocksPerRequest = 2` so that synchronization takes several rounds; the
bounds are checked as invariants on the records in flight, as in the legacy
model.

### Confirmed safe

- **Responder answers before the requester's FIN.** The FIN is consumed by
  `RecvFin` after the response was served; it is never "data after a complete
  request". No protocol error in any configuration.
- **Early-finished `get-blocks` responses.** The requester re-requests the
  remainder; `EventualConsensus` holds, so the re-request loop converges.
- **Refusing streams that arrive before the handshake completes** now also
  covers request streams: the requester observes the responder's reset,
  frees the stream and retries.

### Lesson — refuse is two operations for a reason

The first Phase 2 run failed `EventualConsensus` in the refuse
configuration: a `get-headers` stream refused before the handshake hung
forever and blocked every later request. The model had implemented "refuse"
as STOP_SENDING only. The requester had already finished its sending
direction, so STOP_SENDING told it nothing; only the RESET_STREAM of the
responder's direction — the second half of the draft's definition of
refusing a bidirectional stream ("Stream Types") — lets a requester learn that
its request is dead. Zebra refuses requests with `send.reset(Refused)`, the
half that matters. Worth keeping in mind for any implementation that refuses
streams before reading them.

## Phase 3 — the v2 download scheduler

`v2/sync_scheduler.tla` is the v2 counterpart of the legacy
`sync_scheduler.tla`: same altitude (which peer to ask for each block), same
discipline (the `Holds(p, b)` oracle appears only in invariants), same
switch-plus-configs structure. Zebra's v2 stack defers this layer to a future
"ibd-engine" scheduler, so the model is ahead of the implementation — the
point where findings are cheapest.

### What changes in v2

The legacy scheduler had two uninformative failure outcomes (timeout,
dropped connection). The v2 protocol has four ways a request ends without a
block, and only one carries information about the peer's chain:

| Outcome | Draft source | Registry-relevant? |
|---|---|---|
| per-entry not-found (`0x02`) | "get-blocks" | **yes** — mark missing |
| `REFUSED` stream reset | "Request Streams"; routine under Zebra's 2-bulk-stream cap | no |
| truncation (early FIN after any complete entry) | "get-blocks", "get-block-range" — sanctioned and resumable | no |
| timeout → `CANCELLED` | "Block Download Parameters" | no |

Each uninformative outcome gets a switch that treats it as informative
(`TreatRefusedAsMissing`, `TreatTruncatedAsMissing`, `BuggyTimeout` — the
last is the exact legacy zebra#10679 bug kept as a regression guard). On top
of that, the scheduler applies Zebra's unresponsive-peer rule
(zebra#11276): `UnresponsiveLimit` consecutive timeouts with no response of
any kind disconnects the peer; the `Redial` switch decides whether
disconnected peers come back. Any response — a block, a not-found, a
REFUSED, a truncation — resets the consecutive-timeout count, matching
Zebra's "concurrent timeouts overlapping a response do not count".

### Results

Peer set as in the legacy stall: `p_tip` holds everything, `p_lag` only
block 1, so block 2 has exactly one holder.

| Config | Behaviour | Result |
|---|---|---|
| `sync_scheduler.cfg` | fixed (redial, no poisoning) | 339 states, all invariants + `EventuallyAllVerified` pass |
| `sync_scheduler_refused.cfg` | REFUSED → missing | `RegistryHonest` violated in 2 steps |
| `sync_scheduler_truncated.cfg` | truncation → missing | `EventuallyAllVerified` violated: one truncated response from the only holder of block 2 makes it unroutable |
| `sync_scheduler_timeout.cfg` | timeout → missing | `RegistryHonest` violated in 2 steps (legacy regression guard) |
| `sync_scheduler_evict.cfg` | honest registry, `Redial = FALSE` | `EventuallyAllVerified` violated: two timeouts evict the only holder, and nothing brings it back |

### What this says to an implementer

1. **The legacy lesson triples in v2.** "A timeout is not a notfound" was
   one rule in the legacy scheduler; in v2 the same mistake is available
   three ways, and two of them (`REFUSED`, truncation) are *routine,
   sanctioned responder behaviour* — Zebra itself refuses beyond 2
   concurrent bulk streams and truncates responses at byte budgets. A
   scheduler that penalises routing state on any of them stalls against
   fully conformant peers, no adversary needed.
2. **The redial loop is load-bearing for liveness.** The unresponsive-peer
   eviction rule is fine *only because* disconnected peers are redialled.
   The eviction stall counterexample has an entirely honest registry — the
   liveness argument for the ibd-engine has to include the reconnection
   policy, not just the routing table.

### Fairness note

Strong fairness on `Request`/`DeliverBlock`/`NotFound`/`Reconnect` encodes
"the node keeps trying, willing peers eventually answer, the redial loop
keeps running"; the adversarial outcomes carry no fairness, so an infinite
refusal/truncation/timeout storm is possible but never forced — under it,
`SF(DeliverBlock)` still forces eventual delivery in the fixed
configuration, which is exactly the claim that the fixed design has no
starvation route.

## Phase 4 — misbehavior and banning

`v2/misbehavior.tla` turns the draft's "Misbehavior and Banning" section —
particularly its provability principle and its rationale ("penalties
assigned on weaker evidence are worse than none: they let an attacker …
induce honest nodes to ban one another") — into checkable properties, in the
scheduler module's style: a local node scores its remote peers, and switch
constants select wrong readings of the draft.

### The abstraction

Honest peers may legitimately emit two things a naive receiver is tempted to
punish:

- **divergent headers** — contiguous, valid proof of work, but not
  connecting to the local chain: the peer follows another fork. The draft
  says MUST NOT penalize ("Block Announcements", "Headers-First
  Synchronization").
- **requested invalid blocks** — a block the local node itself requested by
  hash whose content fails consensus validation: the responder served
  exactly the bytes the hash names (e.g. a checkpointed-sync artifact); the
  exemption "Content of requested objects" applies, blame lies with the
  announcer.

Byzantine peers emit the penalty table's provable violations: oversize
get-headers responses (+20), non-contiguous headers (+20), invalid
proof-of-work blocks (+100). Peers may disconnect at will and reconnect
unless banned; whether the score survives a reconnect is the
`PerConnectionScore` switch (the draft wants scores keyed by address for
exactly this reason). Fairness encodes the liveness hypothesis: the
Byzantine peer *keeps* misbehaving and keeps reconnecting — on its own
reconnection specifically, so an honest peer's reconnections cannot
discharge it.

### Results

| Config | Behaviour | Result |
|---|---|---|
| `misbehavior.cfg` | provable-only penalties, address-keyed scores | 22 states; `NoHonestBan`, `BanIsFinal`, `PersistentAttackerBanned` all hold |
| `misbehavior_nonconnecting.cfg` | +20 for non-connecting headers | `NoHonestBan` violated: an honest fork-follower is banned after five divergent responses |
| `misbehavior_requested.cfg` | +100 for a requested invalid block | `NoHonestBan` violated in one step |
| `misbehavior_perconn.cfg` | per-connection score | `PersistentAttackerBanned` violated: emit 20+20, disconnect, reconnect clean, repeat forever |

The two `NoHonestBan` violations are the draft's warning made concrete: both
buggy readings are natural implementation shortcuts (legacy zcashd punished
non-connecting headers in some paths), and either one lets chain divergence
— which an attacker can manufacture — turn honest peers into banned peers.
The `perconn` violation is the draft's argument for address-keyed persistent
scores, reproduced as a five-state loop.

## Addendum — simultaneous dial (Finding 3)

`v2/dial.tla` models the connection-management gap the phase models
deliberately hid behind an atomic `Connect`: the draft's entire rule for
duplicate connections is *"A node SHOULD maintain at most one connection to
a given remote address"* ("Connection Management"), with no word on the
simultaneous-open race or on which connection to keep.

The model: two peers each want a connection to the other; opens and closes
propagate asynchronously, so both can dial before either observes the
duplicate. On observing it, a node applies one of three policies. Results:

| Config | Policy | Result |
|---|---|---|
| `dial_tiebreak.cfg` | keep the connection dialled by the fixed lower peer | 14 states; `EventuallyOneConnection` holds |
| `dial_outbound.cfg` | refuse the inbound duplicate (= keep the locally first) | violated: perpetual flap |
| `dial_inbound.cfg` | accept the inbound, close the own dial | violated: perpetual flap |

The flap: under any **symmetric** policy the two nodes keep *different*
connections — each keeps the one the other closes — so both connections die,
both nodes redial, and adversarial timing repeats the race indefinitely. The
invariant `AtMostOnePerView` (the draft's stated rule, applied locally)
holds throughout: the flap lives entirely in the gap the sentence leaves
open. Only an **asymmetric** convention both sides can compute — e.g. "the
connection dialled by the peer with the lower address survives" — makes them
agree on a survivor.

Two aggravating notes:

- The model assumes the best case, where a node can even *recognize* the
  inbound duplicate. In practice a QUIC inbound arrives from an ephemeral
  UDP port, not the peer's canonical listen address, so matching it to an
  outbound dial already requires an address-book lookup by IP — the draft
  does not say whether "remote address" means the IP or the (IP, port) pair.
- Zebra's v2 draft implementation has no duplicate-address handling at all
  (`peer_set/initialize/v2_transport.rs`, `inbound_admission.rs`): it keeps
  both connections. The only implementation of the SHOULD ignores it —
  fair evidence that the rule as written is not actionable.

Fairness note: the same existential-fairness pitfall as in the misbehavior
module appeared here — weak fairness over "some accept happens" is
discharged by the redial cycle while a specific connection's accept starves.
Fairness is therefore per connection (each specific open, close notice and
settle is eventually processed), and the flap counterexamples contain every
fair action infinitely often.

## Addendum — get-mempool re-subscription (Finding 1 again, and Finding 4)

`v2/mempool_sub.tla` models the draft's other singleton-stream rule
("get-mempool": "A node MUST NOT open more than one concurrent `get-mempool`
stream to the same peer; a second concurrent subscription is a connection
error of type `PROTOCOL_ERROR`") against the cancel/re-subscribe churn the
draft itself anticipates (it recommends rate-limiting it).

**The race (Finding 1's class, second instance).** The requester cancels its
subscription with `CANCELLED` and opens a new `get-mempool` stream; the two
signals travel on different streams, so the responder can observe the new
stream's type byte first. Under the literal text it closes the connection —
against a requester that never had two subscriptions open from its own point
of view. `mempool_strict.cfg` violates `NoHonestProtocolError` in six
states. Zebra's draft implements the strict check
(`mempool_subscribed.swap(true)` → `fail_protocol`) and its conformance
notes lean on "prompt cancel detection" — timing, which the transport does
not guarantee. Two rules of the draft now fail the same way for the same
reason; the fix should be shared.

**Finding 4 — the fix needs stream creation order, which the abstract
stream layer does not provide.** The first tolerant rule tried —
"a newly observed subscription supersedes the one being served" — failed
`EventuallySubscribed`: stream *opens* also reorder, so the stale open of an
already-cancelled subscription can arrive after the live subscription's open
and would supersede it, leaving the requester unsubscribed with no error on
either side. The rule that verifies (`mempool_tolerant.cfg`, 115 states,
complete) is: *a subscription stream supersedes the one being served only if
the peer opened it later; an older stream is refused without penalty.* That
requires the receiver to know the order in which the peer opened its
streams. QUIC provides it (stream IDs are monotone per opener), but the
draft's "Transport Requirements" abstraction only says the receiver "can
tell which peer opened it and of which kind it is" — creation order is not
part of the abstract stream layer, so the working rule cannot be written
against the abstraction, only against QUIC directly. Any transport realizing
the stream layer (the Tor framing included) must guarantee
monotonically-ordered stream identifiers for the fix to be portable.

## Addendum — Byzantine receiver obligations

The phase models check honest interleavings; this addendum adds a
wire-level adversary to `protocol.tla` to check the *receiver's*
obligations. A Byzantine peer completes an honest handshake and then, within
a `MaxMischief` budget, commits four kinds of mischief with opposite
required outcomes:

| Mischief | Draft's required handling | Ghost flag |
|---|---|---|
| second `init` record | connection error `PROTOCOL_ERROR` ("Handshake Validation") | violation |
| stream finished before its type byte | connection error `PROTOCOL_ERROR` ("Stream Types") | violation |
| second handshake stream | connection error `PROTOCOL_ERROR` ("Connection Handshake") | violation |
| unknown stream type | refuse with `UNSUPPORTED_STREAM_TYPE`, MUST NOT close or penalize | none |
| unknown handshake-stream record kind | MUST ignore | none |

Two properties tie them together: `CloseAccountable` — an honest receiver
fires `PROTOCOL_ERROR` only when the ghost flag is set, i.e. never for
tolerated mischief and never spuriously under any interleaving — and
`EventuallyPunished` — every genuine violation eventually ends the
connection. Both hold (`protocol_byzantine.cfg`, 4,295 states, complete;
TLC coverage confirms every mischief action and both punishment branches
fire). All honest-configuration invariants also still hold with the
adversary present, and the full honest regression is unchanged to the
state count.

The negative control `protocol_punish_unknown.cfg` flips the one forbidden
reading (`PunishUnknownType`): treating an unknown stream type as a
connection error breaks `CloseAccountable` in eight states. That MUST NOT
is what lets future stream types deploy without version gating — a receiver
that violates it disconnects the first peer to deploy one.

Verdict: the connection-layer receiver rules are consistent as written —
the model found no way for the adversary to induce an unaccountable close
or to escape punishment for a provable violation. This is a confirmation,
not a finding.

## Addendum — compact block relay (Finding 5)

`v2/compact_relay.tla` models compact block reconstruction between a sender
and a requester: announcements carry per-announcement nonces, the
requester's unmatched transactions are fetched by SHORTID reference, and
the responder interprets those references "using the nonce of the compact
block it most recently sent to the requesting peer for the identified
block" ("Requesting Missing Transactions"). Two sanctioned behaviours make
that interpretation go stale:

1. a sender may announce the same block again with a fresh nonce (for
   example when re-announcing on a replacement announcement stream — the
   very behaviour recommended in item 2 of the feedback);
2. announcements are best-effort, so the re-announcement can be lost while
   the requester is mid-attempt.

After that, every SHORTID reference the requester can ever produce is
stale: each resolves to not-found or, by 48-bit collision, a wrong
transaction (the model resolves the choice adversarially).

| Config | Behaviour | Result |
|---|---|---|
| `compact.cfg` | SHOULD-fallback honoured, MUST-NOT-penalize honoured | 64 states; `EventuallyHasBlock`, `NoHonestPenalty`, `WrongTxNeverAccepted` all hold |
| `compact_nofallback.cfg` | retry the compact path instead of falling back | `EventuallyHasBlock` violated in 7 states: announce, attempt under nonce 1, re-announcement dropped mid-attempt, stale serve fails, nothing left to retry |
| `compact_penalize.cfg` | penalize reconstruction failure | `NoHonestPenalty` violated in 6 states: honest nonce churn frames the sender |

**Finding 5 — the fallback SHOULD does a MUST's job.** Once the requester's
SHORTID view is stale and the fresher announcement is lost, no rule of the
draft other than "the node SHOULD fall back to requesting the full block
via get-blocks" delivers the block; an implementation exercising the
latitude of that SHOULD (for example by retrying the compact path, hoping
for a fresher announcement) stalls against a fully conformant sender. The
penalty MUST NOT, by contrast, is confirmed load-bearing exactly as
written. `WrongTxNeverAccepted` also machine-checks the draft's own
consensus claim: a wrongly matched transaction dies at the merkle check and
never reaches an accepted block.

## Addendum — epoch enforcement (confirmation, with one warning)

`v2/epoch.tla` models network-upgrade activation ("Network Upgrade Epoch
Enforcement"): activation happens at a block height, so a synced node and a
lagging node observe it at different times; each node in the new epoch MUST
drop connections whose negotiated version is below the new minimum, with
`OBSOLETE`.

| Config | Scenario | Result |
|---|---|---|
| `epoch.cfg` | both peers upgraded, one lagging across the activation height | 4 states; the connection is never touched and the laggard catches up |
| `epoch_upgrade.cfg` | old-version peer dropped at activation, upgrades, reconnects | 28 states; passes |
| `epoch_ban.cfg` | the `OBSOLETE` drop also bans the address | `CatchesUp` violated in 3 states |

**Confirmed:** keying enforcement on the handshake-negotiated version — and
never on the peer's chain state — makes divergent activation observation
harmless: an upgraded node arbitrarily far behind the activation height is
never dropped and syncs straight across the boundary. The rule is well
designed.

**Warning (implementation-level):** `OBSOLETE` is a close code, not a
misbehavior verdict — being unupgraded is not a provable violation, and the
draft's banning section reserves bans for those. An implementation that
routes the `OBSOLETE` drop through its ban machinery strands peers: in the
minimal counterexample the banned peer had *already upgraded its software*
when the drop happened, because the stale negotiated version belongs to the
connection (fixed at handshake), not to the peer. A one-line note in the
draft ("a node MUST NOT ban an address merely for advertising an obsolete
protocol version") would foreclose it.

## Addendum — refinement and symbolic checking

### The common abstraction

`v2/protocol.tla` and `v2/sync_scheduler.tla` model the same activity at
different altitudes; `v2/downloader.tla` is the pipeline object they share:
verified blocks, in-flight blocks, and four transitions (request, deliver,
requeue, extend). Both models refine it, TLC-checked:

| Check | Mapping | Result |
|---|---|---|
| `sched_refinement.cfg` | registry, retries, peer identities forgotten; NotFound/Refused/Truncated/Timeout all map to Requeue | 339 states, passes |
| `refinement.cfg` | one pipeline per peer; in-flight = heights in get-blocks request/response records still queued on streams; serve steps stutter (the height moves between records without leaving flight); mining maps to Extend | 327,367 states, complete, passes |

The refinement is safety-only and deliberately so: the buggy scheduler
configurations refine the downloader too — the stall bugs are liveness
bugs, invisible at this altitude. A mutation test (mapping headers records
into the in-flight set) fails the check, confirming it constrains the
mapping. Checked with `MaxBlocksPerRequest = 1` so one concrete step is one
abstract step.

### Apalache: the dual projection

TLC explores every reachable state at one parameter valuation. Apalache
(`v2/sync_scheduler_ind.tla`, Apalache 0.62.1) checks the dual: bounded
depth, all parameter valuations at once — `LagTip`, `MaxRetries`,
`UnresponsiveLimit` symbolic over Nat.

| Check | Result |
|---|---|
| symbolic base, fixed behaviour (`--length=0`) | NoError, seconds |
| symbolic base, ALL switches symbolic (`--length=0`) | NoError, seconds |
| bounded exploration to depth 8, fixed behaviour, `MaxBlock = 2` | NoError, ~3 minutes |
| **inductive step** (`IndInv /\ Next => IndInv'` from arbitrary `Gen` states), fixed behaviour, `MaxBlock = 4` | **NoError, one ~3-hour Z3 solve** |
| satisfiability canary (`SatCanary = FALSE` over `IndInit`) | violated in seconds — `IndInit` admits states, the induction is not vacuous |

Together the base and step checks prove `IndInv` — `TypeOK`,
`RegistryHonest`, `RegistryHasIsSound`, `VerifiedAreReal` — is an
**inductive invariant** of the fixed scheduler at `MaxBlock = 4`: it holds
at every depth, for every `LagTip`, `MaxRetries` and `UnresponsiveLimit`
in Nat. That is a claim TLC cannot make (it fixed all three constants and
`MaxBlock = 2`). The depth-8 bounded run is the quick reproducible check
for anyone unwilling to spend hours of solver time. Two
tool limitations found on the way, recorded for reuse: symbolic integer
ranges (`1..N` with symbolic `N`) are unsupported anywhere, and `@type`
annotations attach correctly only in the single `CONSTANTS`-block
declaration style. Apalache runs are local-only — SMT solve times are too
machine-dependent for CI — with the module, config and exact commands in
the repository. (An earlier revision of this section reported the
induction step as impractical; the long solve later completed with
NoError, and the canary confirmed non-vacuity.)
