<!--
DRAFT comment for https://github.com/zcash/zips/pull/1344 — not posted.
Short pointer form: the findings document in this repository is the source
of truth; this comment only lists them. Edit freely, then paste.
-->

Following the "Formal Model" section's pointer to
[zcash-p2p-spec](https://github.com/oxarbitrage/zcash-p2p-spec): the TLA+
model has been extended to this draft (revision `a3f4fa2a`). It covers the
stream layer, handshake, announcement and request streams, headers-first
sync, the download scheduler, misbehavior and banning, connection
management, `get-mempool`, compact block relay, epoch enforcement, the Tor
framing layer and the bulk-sync primitives — about 60 TLC checks run in
CI, plus an Apalache induction proof of the scheduler's safety invariants.

Most of the draft verifies as written (the provability principle and its
exemptions, the forward-compatibility MUST NOTs, refuse-as-two-operations,
the deferred `get-hashes` penalties, epoch enforcement, the short-ID
consensus claim). Where the model found problems, each comes with a
reproducible counterexample and proposed wording, in
**[`documents/v2-spec-feedback.md`](https://github.com/oxarbitrage/zcash-p2p-spec/blob/main/documents/v2-spec-feedback.md)**
(rationale in [`v2-modeling.md`](https://github.com/oxarbitrage/zcash-p2p-spec/blob/main/documents/v2-modeling.md)).
In brief:

1. **Singleton-stream rules race with stream independence** ("Announcement
   Streams", "get-mempool"): a sender replacing a finished/cancelled stream,
   as allowed, is disconnected with `PROTOCOL_ERROR` when the receiver sees
   the replacement before the old stream's FIN. Impossible on Tor (ordered),
   reachable on QUIC. `v2/protocol_strict.cfg`, `v2/mempool_strict.cfg`.
2. **The natural fix needs stream creation order**, which "Transport
   Requirements" doesn't expose (QUIC stream IDs do). An order-blind
   supersede rule fails liveness. `v2/mempool_tolerant.cfg`.
3. **"At most one connection per remote address" has no tie-break**: every
   symmetric policy flaps forever under a simultaneous dial.
   `v2/dial_outbound.cfg`, `v2/dial_inbound.cfg`.
4. **Compact-block reconstruction fallback is a SHOULD doing a MUST's
   job**: after nonce churn plus a lost re-announcement it is the only
   rule that delivers the block. `v2/compact_nofallback.cfg`.
5. **`initial_max_data` has no floor** (Tor preamble): sub-record
   connection credit wedges a record-granularity receiver.
   `v2/framing_wedge.cfg`.
6. **Stream limits: "concurrent" in the preamble, cumulative in the
   framing section** — the readings stall silently or disconnect honest
   peers. `v2/framing_noraise.cfg`, `v2/framing_concurrent.cfg`.
7. Smaller: `txouts` is hash-determined and relied upon but absent from
   the penalty table; `OBSOLETE` should be explicitly non-bannable
   (`v2/epoch_ban.cfg`); the `get-block-range` first-block exemption must
   be symmetric (`v2/block_range_firstflood.cfg`).

Plus a note for the sync draft: only the explicit not-found result may
mark a peer as lacking a block — `REFUSED` and truncation are sanctioned
outcomes — and unresponsive-peer eviction is liveness-sound only with
redial (`v2/sync_scheduler_*.cfg`).

Happy to file these as separate issues, or send wording as a PR against
the branch once you've picked a direction on 1, 3 and 6.
