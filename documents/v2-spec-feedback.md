# Feedback for zcash/zips#1344 from the TLA+ model

**Snapshot:** against draft revision `a3f4fa2a` (the revision Zebra's
`SPEC-CONFORMANCE.md` pins), as of 2026-08-25. If the draft has moved,
section names and line references may have shifted; the configs named
below re-check each item and are run by this repository's CI on every push.

Each item has a reproducible TLC counterexample in `v2/`
(`cd v2 && java -jar ../tla2tools.jar -config <cfg> <module>.tla`; the
named "strict"/"buggy" configs are expected to fail — they are the
counterexamples — and the matching tolerant/fixed configs pass). The
modeling rationale for every item is in [`v2-modeling.md`](v2-modeling.md).
Wording proposals are suggestions only.

Summary — items proposing a change: 1, 2, 7, 8, 10, 11, 12, 13, 14, and 5
(addressed to the sync draft / scheduler rather than this ZIP). Items 3,
4, 6, 9 are confirmations that the text holds as written.

## 1. "Announcement Streams": replacement streams race with the singleton rule

**Text.** "A node MUST NOT open more than one announcement stream of a given
type in the same direction at a time. A second concurrent stream of the same
type is a connection error of type `PROTOCOL_ERROR`. If an announcement stream
is reset or finished, the sender MAY open a replacement."

**Problem.** "Transport Requirements" guarantees that streams are mutually
independent. A sender that finishes (or resets) its announcement stream of
type *t* and opens a replacement has, from its own point of view, never had
two open at a time. The receiver, however, may consume the replacement's type
byte before it reads the old stream's FIN (or observes its reset, which is
not even ordered with the data). At that moment it sees two open streams of
type *t* from the same peer and the text tells it to close the connection.
The receiver cannot distinguish this from a genuine violation.

TLC finds the 12-state counterexample with `v2/protocol_strict.cfg`
(`NoHonestProtocolError` violated); every step is a MAY-sanctioned action.
Zebra's draft implementation (`read_inbound_announcement_stream`) applies the
strict reading; its own sender never triggers it, so the hazard is between
implementations.

**Proposal.** Replace the connection-error sentence with a superseding rule:

> A node receiving an announcement stream of type *t* from a peer while an
> earlier stream of type *t* from that peer is still open MUST treat the
> earlier stream as finished by its sender: it SHOULD read and process the
> earlier stream's remaining records up to its FIN or reset, and MUST NOT
> treat the pair as a connection error. A sender MUST NOT write further
> records on an announcement stream after opening its replacement.

The stream concurrency limit ("Transport Requirements") already bounds what a
misbehaving peer can do with extra announcement streams, so the strict rule
buys no protection.

## 2. "Announcement Streams" / "Block Announcements": re-announce after a reset

A RESET_STREAM can overtake records already written on the stream. A sender
that resets its block announcement stream after announcing a block, and then
opens a replacement, has announced that block to nobody. The draft calls
announcements best-effort, and the peer recovers through a later
`get-headers`, so this is not an error — but a one-line recommendation would
avoid a silent propagation gap:

> A node that opens a replacement block announcement stream SHOULD announce
> its current chain tip on it.

(Found because the model's liveness property `AnnouncementsFlow` failed
until the sender was made to do this.)

## 3. Confirmed safe: streams arriving before the handshake completes

"Connection Handshake" lets a node either buffer or refuse (with `REFUSED`)
streams that arrive before its handshake is complete. Because the peer's
`init` and its first announcement streams travel on different streams, the
announcement streams can legitimately arrive first. The model checks both
choices (`v2/protocol.cfg`, `v2/protocol_refuse.cfg`): neither leads to a
protocol error, and the refuse/reopen loop terminates once the `init` is
processed. No change needed; a non-normative note that this ordering is
expected might help implementers.

## 4. Confirmed safe: request stream rules under reordering

Modeled in Phase 2 (`v2/protocol.cfg`, complete state space):

- A responder that begins serving as soon as the request is syntactically
  complete, before the requester's FIN arrives ("Request Streams"), never
  produces a protocol error on either side.
- A `get-blocks` responder that finishes after any complete entry is handled
  by re-requesting the remainder, and synchronization still converges.
- The two-operation definition of *refuse* for bidirectional streams ("Stream
  Types": cancel the peer's direction **and** reset our own) is necessary, not
  belt-and-braces: a requester has already finished its sending direction, so
  only the reset tells it the request is dead. A model that omitted the reset
  hung every subsequent request. A non-normative sentence saying why both
  operations are required might save an implementer the same mistake.

## 5. For the sync draft / ibd-engine rather than the transport ZIP

The Phase 3 scheduler model (`v2/sync_scheduler.tla`) yields two
requirements any conforming download scheduler must meet, reproducible as
TLC counterexamples when violated:

- Only the explicit per-entry not-found result may mark a peer as lacking a
  block. `REFUSED` resets and truncated (early-finished) responses are
  routine, sanctioned responder behaviour; recording them as not-found
  stalls synchronization against fully conformant peers. This generalizes
  the legacy "a timeout is not a notfound" rule (zebra#10679) to the v2
  outcome set. A sentence in the sync recommendations draft would pin this.
- An unresponsive-peer disconnection rule (as in Zebra's v2 connection,
  zebra#11276) is sound for liveness only together with a reconnection
  policy: evicting the sole holder of a block with no redial stalls the
  sync even with an honest registry.

## 6. Confirmed: the misbehavior section's rules are load-bearing

The Phase 4 model (`v2/misbehavior.tla`) confirms three of the draft's
misbehavior rules by violating them:

- Penalizing non-connecting headers — forbidden by the draft, but a natural
  shortcut — bans an honest peer on another fork after five responses.
- Penalizing consensus invalidity of a block the node itself requested by
  hash — against the "Content of requested objects" exemption — bans an
  honest peer in one step.
- Per-connection scores instead of address-keyed persistent scores let a
  persistent attacker shed its score by reconnecting below the threshold,
  forever.

No draft change needed; these support the text as written.

## 7. "Connection Management": the duplicate-connection rule needs a tie-break

**Text.** "A node SHOULD maintain at most one connection to a given remote
address."

**Problem.** The sentence does not address the simultaneous-open race: two
nodes dial each other at once, so two connections exist before either side
can observe the duplicate. TLC (`v2/dial.tla`) shows that any *symmetric*
resolution policy — keep the outbound, keep the inbound, keep the locally
first — is self-defeating when both peers apply it: each keeps the
connection the other closes, both connections die, both nodes redial, and
the race can repeat indefinitely. The stated rule is satisfied throughout;
the flap lives in what the sentence does not say. Only an asymmetric
convention both sides can compute converges (`dial_tiebreak.cfg`).

Zebra's v2 draft currently implements no deduplication at all — both
connections persist — so today the SHOULD is simply unmet.

**Proposal.** Either specify the convention, e.g.:

> If a node observes two connections to the same remote address (for
> example after a simultaneous dial), the connection initiated by the peer
> whose canonical address is numerically lower survives; the node SHOULD
> close the other with `NO_ERROR`. A node MUST NOT treat the duplicate as a
> protocol error.

or explicitly permit coexistence ("a node MAY keep both connections until
one idles out") so that implementations that do deduplicate cannot flap
against ones that do not. Also worth clarifying whether "remote address"
means the IP or the (IP, port) pair, since inbound connections arrive from
ephemeral ports.

## 8. "get-mempool": the singleton rule races like item 1, and the fix
## needs stream creation order

**Text.** "A node MUST NOT open more than one concurrent `get-mempool`
stream to the same peer; a second concurrent subscription is a connection
error of type `PROTOCOL_ERROR`."

**Problem A — the same race as item 1.** A requester that cancels its
subscription with `CANCELLED` and re-subscribes (churn the section itself
anticipates and answers with a rate-limit recommendation) can have the new
stream's type byte observed before the old stream's cancel: the responder
then sees "a second concurrent subscription" from a conformant peer and
disconnects it. TLC reproduces it in six states
(`v2/mempool_strict.cfg`). This is the second rule in the draft with this
shape (item 1 is the first); a shared fix is warranted.

**Problem B — the natural fix is not implementable against the abstract
stream layer.** The obvious repair — treat the newer subscription stream as
superseding the served one, and refuse a stale older one without penalty —
requires the receiver to order the peer's streams by creation. An
order-blind supersede rule verifiably fails: stream opens also reorder, so
a stale open can supersede the live subscription and leave the requester
silently unsubscribed (found as a TLC liveness violation). QUIC exposes the
needed order (stream IDs are monotone per opener), but "Transport
Requirements" only guarantees that the receiver can tell *who* opened a
stream and *of which kind it is* — not *in what order*. Suggested changes:

> In "Transport Requirements", add: "The receiver of a stream can tell the
> order in which its peer opened its streams." (QUIC: by stream ID; any
> other transport realizing the stream layer must provide the same.)
>
> In "get-mempool" (and analogously for announcement streams, item 1):
> "A node observing a new `get-mempool` stream while serving an earlier one
> from the same peer MUST treat the stream the peer opened later as the
> live subscription: it SHOULD reset the superseded stream, MUST refuse a
> stream older than one it is already serving with `CANCELLED` and no
> penalty, and MUST NOT treat either case as a connection error."

## 9. Confirmed: the connection-layer receiver obligations are consistent

A wire-level adversary model (`v2/protocol_byzantine.cfg`) checked the
receiver rules jointly: second `init` records, premature FINs and second
handshake streams are always punished with `PROTOCOL_ERROR`; unknown stream
types and unknown handshake-record kinds are always tolerated; and no
interleaving produces a close without a genuine violation. All hold. The
negative control shows the forward-compatibility MUST NOT ("Stream Types")
is load-bearing: a receiver that closes on unknown stream types would
disconnect the first peer to deploy a future stream type. No change needed.

## 10. "Relay Protocol": the reconstruction fallback should be a MUST

**Text.** "…the node SHOULD fall back to requesting the full block via
`get-blocks`, and MUST NOT assign a misbehavior penalty solely because
reconstruction failed."

**Problem.** Two sanctioned behaviours can permanently invalidate a
requester's SHORTID view of a block: the sender re-announces it with a
fresh nonce (SHORTID references are interpreted under "the nonce of the
compact block most recently sent"), and the fresher announcement is dropped
as best-effort while the requester is mid-attempt. From then on every
SHORTID reference the requester can produce answers not-found. TLC
(`v2/compact_nofallback.cfg`) shows a requester that exercises the SHOULD's
latitude — retrying the compact path instead of falling back — never
obtains the block from a fully conformant sender: the fallback is the only
guaranteed delivery path, i.e. a SHOULD doing a MUST's job. Suggest:

> …the node MUST obtain the block by other means, normally a `get-blocks`
> request, and MUST NOT assign a misbehavior penalty solely because
> reconstruction failed.

Related: re-announcing a block on a replacement announcement stream (item
2) increases nonce churn, so items 2 and 10 should land together. The
penalty MUST NOT is confirmed as written (`v2/compact_penalize.cfg`), and
the draft's consensus claim for short-ID collisions is machine-checked
(`WrongTxNeverAccepted`).

## 11. Epoch enforcement confirmed; suggest forbidding bans on OBSOLETE

Modeled in `v2/epoch.tla`. Keying epoch enforcement on the negotiated
version (never the peer's chain state) is confirmed sound: upgraded peers
are never dropped however divergently they observe activation, and a
dropped old-version peer that upgrades reconnects and catches up.

One suggested addition: nothing currently says the `OBSOLETE` disconnect
must not be treated as ban-worthy. An implementation that bans the
addresses it drops at activation strands peers — provably including peers
whose software was already upgraded when the drop fired, since the stale
negotiated version belongs to the connection, not the peer
(`v2/epoch_ban.cfg`, 3-state counterexample). Suggest, in "Network Upgrade
Epoch Enforcement" or "Misbehavior and Banning":

> A node MUST NOT ban an address merely because a peer at that address
> advertised an obsolete protocol version.

## 12. "Connection Preamble": give `initial_max_data` the same floor as
## `initial_max_stream_data`

The preamble mandates `initial_max_stream_data` >= 2,228,224 bytes so a
maximum record can always traverse a stream — but sets no minimum for the
connection-level `initial_max_data`. TLC (`v2/framing_wedge.cfg`) shows
two conforming peers wedging forever: one advertises less than a record
of connection credit, the other raises `MAX_DATA` only after processing a
complete record. Suggest:

> A node MUST allow an `initial_max_data` of at least 2,228,224 bytes.

## 13. "Connection Preamble" / "Stream Framing": concurrent vs cumulative
## stream limits

The preamble describes `initial_max_streams_bidi`/`_uni` as limits "on
the peer's concurrent ... streams"; the framing section defines
`MAX_STREAMS_*` as raising the limit on the peer's *cumulative* count of
opened streams (QUIC's semantics). The readings disagree in both
directions, reproducibly (`v2/framing_noraise.cfg`: silent announcement
stall; `v2/framing_concurrent.cfg`: honest peer disconnected with
`PROTOCOL_ERROR`). Suggest rewording the preamble fields as "initial
limit on the peer's cumulative count of opened ... streams", plus a
sentence noting that a receiver maintains an effective concurrency limit
by raising the cumulative limit as streams close.

Also relevant to item 1: the model confirms the announcement-replacement
race cannot occur on the Tor transport (the pipe is ordered, FIN precedes
the replacement), so the singleton rule's literal reading is safe on Tor
and fails only on QUIC — the fix belongs in the transport-independent
sections, not the transport ones.

## 14. "get-hashes" / "get-block-range": two small completions

- `txouts` is determined by the block hash exactly as `txs` is, and the
  draft has the requester rely on it (cumulative `txouts` positions the
  spentness-hint bitmap of the sync draft) — yet it appears in neither
  the verify-and-penalize sentence of "get-hashes" nor the penalty table
  ("Misbehavior and Banning" lists only `txs` and `notes`). A lying
  `txouts` misaligns the bitmap with no recourse. Suggest adding `txouts`
  to both, or stating why it is exempt.
- The first-block exemption from `max_bytes` must be implemented
  identically by responder (stopping rule) and requester (FLOOD rule).
  TLC (`v2/block_range_firstflood.cfg`) shows the natural off-by-one — a
  requester counting the first delivered block against the budget —
  disconnects an honest responder that delivers an over-budget anchor
  block exactly as the draft requires. A non-normative sentence noting
  the symmetry would prevent it. The resumption arithmetic itself
  verifies exactly (`v2/block_range.cfg`), and the deferred hint-penalty
  rules of "get-hashes" — including the size/eviction-primitive MUST NOT
  — are confirmed load-bearing as written (`v2/hashes_hints_*.cfg`).
