<!--
DRAFT comment for https://github.com/zcash/zips/pull/1344 — not posted.
Review, edit freely, then paste as a PR comment. Items reference sections
of the draft at revision a3f4fa2a. Everything is reproducible from
https://github.com/oxarbitrage/zcash-p2p-spec (v2/ directory); every
finding below is a TLC counterexample that CI re-checks on each push.
-->

Following up on the "Formal Model" section, which cites
[zcash-p2p-spec](https://github.com/oxarbitrage/zcash-p2p-spec) as the
legacy protocol's TLA+ model: the model has now been extended to this
draft (revision `a3f4fa2a`, the same one Zebra's `SPEC-CONFORMANCE.md`
pins). It covers the stream layer, handshake, announcement and request
streams, headers-first sync, the download scheduler, misbehavior and
banning, connection management, `get-mempool`, compact block relay, epoch
enforcement, the Tor framing layer, and the bulk-sync primitives — about 60
TLC checks run in CI, plus an Apalache induction proof of the scheduler's
safety invariants. Details and every counterexample are in
[`documents/v2-modeling.md`](https://github.com/oxarbitrage/zcash-p2p-spec/blob/main/documents/v2-modeling.md);
full proposed wording is in
[`documents/v2-spec-feedback.md`](https://github.com/oxarbitrage/zcash-p2p-spec/blob/main/documents/v2-spec-feedback.md).

Most of the draft held up: the provability principle, the exemptions, the
forward-compatibility MUST NOTs, refuse-as-two-operations, the deferred
`get-hashes` penalties, epoch enforcement keyed on the negotiated version,
and the short-ID consensus claim all verify as written (and the model
breaks when any of them is weakened). The items below are where it found
a problem. I'd be glad to file any of these as separate issues if that's
easier to track.

### 1. Singleton-stream rules race with stream independence ("Announcement Streams", "get-mempool")

"A second concurrent stream of the same type is a connection error of type
`PROTOCOL_ERROR`" (and the identical rule for `get-mempool`) disconnects
conformant peers: a sender finishes or resets an announcement stream and
opens the replacement the same paragraph allows; because streams are
mutually independent ("Transport Requirements"), the receiver may consume
the replacement's type byte before the old stream's FIN or reset, and at
that moment sees two open streams. Every step of the 12-state trace is a
MAY-sanctioned action (`v2/protocol_strict.cfg`); the `get-mempool`
cancel/re-subscribe variant is 6 states (`v2/mempool_strict.cfg`). Zebra's
draft implements the strict reading on receive in both places; its own
sender never triggers it, so the hazard is between implementations.

The race is *impossible* on the Tor transport (ordered pipe: FIN always
precedes the replacement), which may be how the rule got written — but it
means the fix belongs in the transport-independent text.

Proposed: replace the connection-error sentence with a superseding rule —
a newly opened stream of type *t* from a peer supersedes the earlier
stream of type *t* being served; the receiver drains the earlier one to
its FIN/reset and MUST NOT treat the pair as a connection error. Stream
concurrency limits already bound what a misbehaving peer gains.

### 2. The supersede fix needs stream creation order, which the abstract stream layer doesn't expose

An order-blind "the new stream supersedes" rule verifiably fails: stream
*opens* also reorder, so the stale open of an already-cancelled
subscription can arrive after the live one's and supersede it, leaving the
requester silently unsubscribed (liveness violation). The rule that
verifies (`v2/mempool_tolerant.cfg`) compares the order in which the peer
opened its streams. QUIC provides that (stream IDs are monotone per
opener), but "Transport Requirements" only guarantees the receiver can
tell *who* opened a stream and *of which kind* — not in what order.

Proposed: add to "Transport Requirements": "The receiver of a stream can
tell the order in which its peer opened its streams." Any transport
realizing the stream layer must then provide it (the Tor framing already
does via sequential stream IDs).

### 3. "Connection Management": the duplicate-connection rule needs a tie-break

"A node SHOULD maintain at most one connection to a given remote address"
doesn't address the simultaneous open. Any *symmetric* resolution policy —
keep the outbound, keep the inbound, keep the locally first — is
self-defeating when both peers apply it: each keeps the connection the
other closes, both die, both redial, and adversarial timing repeats the
race indefinitely, while the stated rule holds throughout
(`v2/dial_outbound.cfg`, `v2/dial_inbound.cfg`). Only an asymmetric
convention converges (`v2/dial_tiebreak.cfg`). Zebra's draft currently
doesn't deduplicate at all.

Proposed: either specify the convention (e.g. "the connection initiated
by the peer whose canonical address is numerically lower survives; close
the other with `NO_ERROR`; never a protocol error") or explicitly permit
coexistence. Also clarify whether "remote address" is the IP or the
(IP, port) pair — inbound QUIC arrives from ephemeral ports.

### 4. "Relay Protocol": the reconstruction fallback should be a MUST

SHORTID references are interpreted under "the nonce of the compact block
most recently sent". A re-announcement with a fresh nonce (e.g. on a
replacement announcement stream) that is then dropped as best-effort
leaves every SHORTID reference the requester can produce stale. From
then on, "the node SHOULD fall back to requesting the full block via
`get-blocks`" is the *only* rule that delivers the block — a requester
exercising the SHOULD's latitude never obtains it from a fully conformant
sender (`v2/compact_nofallback.cfg`). Proposed: "MUST obtain the block by
other means, normally a `get-blocks` request". Relatedly, a sender that
opens a replacement block-announcement stream SHOULD re-announce its tip
on it — a reset can overtake records in flight.

### 5. "Connection Preamble": `initial_max_data` has no floor

The preamble floors `initial_max_stream_data` at 2,228,224 bytes so a
maximum record can traverse a stream, but sets no minimum for the
connection-level `initial_max_data`. A peer advertising less than one
record of connection credit, talking to a receiver that raises `MAX_DATA`
at record granularity (records are the natural unit of processing),
wedges the connection forever with both peers conforming
(`v2/framing_wedge.cfg`; byte-granularity granting passes). Proposed: "A
node MUST allow an `initial_max_data` of at least 2,228,224 bytes."

### 6. "Connection Preamble" vs "Stream Framing": concurrent vs cumulative stream limits

The preamble describes `initial_max_streams_bidi`/`_uni` as limits on the
peer's *concurrent* streams; the framing section defines `MAX_STREAMS_*`
as raising the limit on the peer's *cumulative* count of opened streams
(QUIC's semantics). Both readings are implementable and disagree in both
directions: a concurrent-reading receiver never raises the limit and the
sender's announcement-stream replacements silently stop
(`v2/framing_noraise.cfg`); a concurrent-reading sender exceeds the
cumulative count and is disconnected with `PROTOCOL_ERROR`
(`v2/framing_concurrent.cfg`). Proposed: word the preamble fields as
"initial limit on the peer's cumulative count of opened … streams", and
note that a receiver maintains an effective concurrency limit by raising
the cumulative limit as streams close.

### 7. Smaller completions

- **`txouts`** is determined by the block hash exactly as `txs` is, and the
  requester relies on it (spentness-hint bitmap), yet it is in neither the
  verify-and-penalize sentence of "get-hashes" nor the penalty table.
- **`OBSOLETE` should be explicitly non-bannable.** Nothing says the epoch
  disconnect isn't ban-worthy; an implementation that bans on it strands
  peers — provably including peers that had *already upgraded* when the
  drop fired, since the stale negotiated version belongs to the connection
  (`v2/epoch_ban.cfg`). Suggested: "A node MUST NOT ban an address merely
  because a peer at that address advertised an obsolete protocol version."
- **`get-block-range` first-block exemption** must be implemented
  symmetrically by responder (stopping rule) and requester (FLOOD rule);
  the natural off-by-one — counting the first delivered block against
  `max_bytes` — disconnects an honest responder that delivers an
  over-budget anchor block as required (`v2/block_range_firstflood.cfg`).
  A non-normative sentence would prevent it.

### For the sync draft / scheduler rather than this ZIP

The scheduler model (`v2/sync_scheduler.tla`) generalizes the legacy
"a timeout is not a notfound" lesson (zebra#10679): in v2 only the
explicit per-entry not-found may mark a peer as lacking a block —
`REFUSED` resets and truncated responses are routine, sanctioned responder
behaviour, and recording either as not-found stalls sync against fully
conformant peers. And an unresponsive-peer disconnection rule is
liveness-sound only together with a redial policy. Both are reproducible
stalls; worth a sentence in the sync recommendations.

---

Reproduce any item with `cd v2 && java -jar ../tla2tools.jar -config
<cfg> <module>.tla`; the named configs are expected to *fail* (they are
the counterexamples), and the matching tolerant/fixed configs pass. Happy
to adjust the model if I've misread any section.
