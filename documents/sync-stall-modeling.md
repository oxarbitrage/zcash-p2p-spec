# Modeling the genesis-to-tip sync stall

This note explains how the Zebra "sync stall" — the genesis-to-tip freeze fixed in
[ZcashFoundation/zebra#10679](https://github.com/ZcashFoundation/zebra/pull/10679)
(symptom thread [#5709](https://github.com/ZcashFoundation/zebra/issues/5709)) — is
captured as a TLA+ model in this project, why it does **not** live in
[`protocol.tla`](../protocol.tla), and what the model buys us going forward.

The companion spec is [`sync_scheduler.tla`](../sync_scheduler.tla), checked with
[`sync_scheduler_buggy.cfg`](../sync_scheduler_buggy.cfg) and
[`sync_scheduler_fixed.cfg`](../sync_scheduler_fixed.cfg).

## The bug, in one paragraph

During initial sync a Zebra node downloads blocks from a *pool* of peers, routed by
an inventory registry that records which peer has which block. Three latent defects
combined to turn transient network hiccups into a permanent stall:

1. **Registry poisoning.** The router marked a block "missing on peer P" on *any*
   request failure — including timeouts and dropped connections, not just an explicit
   `notfound`. Once every peer holding a block was poisoned by a transient error,
   `getdata` could no longer be routed to a peer that actually had it.
2. **Silent drop.** A download that failed with `NotFound` was discarded instead of
   re-queued. A single frontier block stuck at the checkpoint boundary was never
   re-fetched, permanently wedging the verify pipeline.
3. **Batch abandonment.** One `DuplicateBlockQueuedForDownload` in a batch dropped the
   rest of the batch, leaving frontier gaps.

These stayed invisible until blocks took 5–8 minutes to verify (the "sandblasting era")
on a degraded peer set where only 2–5% of peers were at-tip. The fix (a) marks inventory
missing only on an explicit `notfound`, and (b) re-queues `NotFound` blocks with a bounded
retry count, routed away from the `notfound` peer.

## Why it is not in `protocol.tla`

`protocol.tla` models a **single connection between two peers**: handshake → keepalive →
a direct `inv`/`getheaders`/`headers`/`getdata`/`block` loop → timeout disconnect. Sync is
point-to-point — peer *n* learns peer *m* is ahead and pulls blocks straight from *m*.

The stall lives one layer up, in the **download scheduler and its inventory-routing
registry across a pool of peers** — machinery that has no representation in the
connection-level model. There is no registry to poison and no routing decision to get
wrong when there is only ever one source. So the bug is added as a *new* module at the
scheduler altitude, not as an edit to the existing connection model. The two compose:
`protocol.tla` is *how one connection behaves*; `sync_scheduler.tla` is *how the node
chooses which connection to ask for each block*.

## The abstraction

A single local syncer downloads a fixed set of blocks `1..MaxBlock` from a set of `Peers`.

| Concept | Model |
|---|---|
| Ground truth: which peer holds which block | `Holds(p, b) == b ≤ PeerTip(p)` — lagging peers (`LaggingPeers`) hold only up to `LagTip`; others are at tip |
| Inventory routing registry | `avail[p][b] ∈ {"has", "missing", "unknown"}` |
| Work set the scheduler still wants | `pending ⊆ Blocks` |
| Outstanding request | `inflight[b] ∈ Peers ∪ {NONE}` |
| Verified frontier | `verified ⊆ Blocks` |
| Bounded re-queue | `retries[b] ∈ 0..MaxRetries` |

Actions:

- **`Request`** — route a `getdata` for a pending block `b` to a peer `p` *not already
  marked missing* for `b` (`avail[p][b] ≠ "missing"`). This is the routing decision the
  registry poisons.
- **`DeliverBlock`** — the in-flight peer genuinely holds `b`: it is verified and the
  registry correctly records `"has"`.
- **`NotFound`** — the in-flight peer genuinely lacks `b` and says so. Marking it
  `"missing"` is *correct*. What happens to the block then is the `BuggyDrop` switch:
  silently dropped, or re-queued under the retry bound.
- **`TransientError`** — *any* in-flight request may time out or drop, independent of
  whether the peer has the block. The block is re-queued; the `BuggyRouting` switch
  decides the registry entry — poisoned (`"missing"`) or left `"unknown"`.

Two boolean constants select Zebra's pre- and post-fix behaviour:

```
BuggyRouting = TRUE   transient error marks the peer missing  (the poisoning bug)
             = FALSE  transient error leaves the entry unknown

BuggyDrop    = TRUE   notfound silently drops the block       (the wedge bug)
             = FALSE  notfound re-queues with bounded retries
```

## What the model checks

The model catches the bug two ways — a cheap safety smell and the real liveness harm:

1. **`RegistryHonest`** (safety): `avail[p][b] = "missing" ⇒ ¬Holds(p, b)` — the registry
   never marks a peer missing for a block it actually has. Under `BuggyRouting` a transient
   error on a holder violates this *immediately*; TLC returns a two-step counterexample.
   This is the formal statement of "a timeout is not a `notfound`."
2. **`EventuallyAllVerified`** (liveness): `<>(verified = Blocks)` — every block is
   eventually downloaded and verified. Under the buggy switches TLC produces the genesis-to-tip
   stall as a counterexample: each holder of a block is poisoned by a transient error, the
   remaining peers genuinely lack it and `notfound`, the block is silently dropped, and the
   frontier wedges forever.

Strong fairness on `Request`, `DeliverBlock`, and `NotFound` encodes the real-world
assumption that the node keeps trying and a willing peer eventually responds; `TransientError`
gets **no** fairness — it is adversarial-but-optional. Under the fixed switches both
properties hold: poisoning never happens, dropped blocks are re-queued, and the frontier
always completes.

## Results

TLC halts on the first invariant violation, so the poisoning safety smell and the
liveness stall are demonstrated by separate configs (both with the buggy switches on):

| Config | Switches | Checks | Result |
|---|---|---|---|
| `sync_scheduler_poison.cfg` | buggy | `RegistryHonest` | **violated** — 2-step trace (transient error poisons a holder) |
| `sync_scheduler_buggy.cfg` | buggy | `EventuallyAllVerified` | **violated** — the stall: block dropped, frontier wedges |
| `sync_scheduler_fixed.cfg` | fixed | all invariants + liveness | holds |

```bash
java -jar tla2tools.jar -config sync_scheduler_poison.cfg sync_scheduler.tla  # expect RegistryHonest violation
java -jar tla2tools.jar -config sync_scheduler_buggy.cfg  sync_scheduler.tla  # expect liveness stall
java -jar tla2tools.jar -config sync_scheduler_fixed.cfg  sync_scheduler.tla  # expect success
```

The liveness counterexample is a five-state stall: request block 1 from `p_tip`,
request block 2 from `p_lag` (which lacks it), deliver block 1, `p_lag` returns
`notfound` for block 2 — which is silently dropped — and the run stutters forever with
`verified = {1}`, never `{1, 2}`.

## Answers to the original questions

- **Can we simulate the problem?** Yes. `sync_scheduler_buggy.cfg` reproduces it as a TLC
  counterexample, and `sync_scheduler_fixed.cfg` shows the fix closes it. The model
  distinguishes the buggy and fixed designs — which is the whole point.
- **Should we update the p2p ZIP?** No normative change. ZIP-204 describes the *wire
  protocol*; the stall is an implementation-level inference bug (treating "no response" as
  "`notfound`"). At most a clarifying note that *absence of a response must not be treated
  as `notfound`* for inventory routing — guidance, not protocol.
- **Can we avoid similar issues by modeling in TLA?** Yes. The reusable guard is
  `RegistryHonest` plus a download-pipeline progress property: *no transient failure can
  permanently remove a block from the set of fetchable blocks.* Once that harness exists it
  defends against the whole class of "transient error poisons routing / silently drops work"
  regressions, not just this one.

## Possible extensions

- **In-order frontier commit.** Model verification as requiring blocks in height order so a
  low stuck block blocks all higher ones — closer to the real checkpoint-boundary wedge.
- **Batch dispatch (mode 3).** Model `getdata` batches and the `DuplicateBlockQueuedForDownload`
  drop. Lower modeling value — more implementation-specific than the routing/registry logic.
- **Compose with `protocol.tla`.** Drive `sync_scheduler` requests through real connection
  state machines so a `Disconnect` is the source of the `TransientError`.
