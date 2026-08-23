# Modeling the version 2 P2P protocol (draft ZIP)

Draft under model: *Version 2 Zcash P2P Network Protocol*,
[zcash/zips#1344](https://github.com/zcash/zips/pull/1344), file
`zips/draft-arya-jvff-p2p-quic-transport.md`, pinned at revision **`a3f4fa2a`**
(the revision Zebra's `SPEC-CONFORMANCE.md` is written against). The draft is
still moving; section names below refer to that revision. The draft's
`# Formal Model` section cites this repository and notes that the model had
not yet been updated for the new protocol — this document describes that
update, phase by phase.

Reference implementation consulted: Zebra's five-PR draft stack
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

## Next phases

- **Phase 2** — request streams (`get-headers`, `get-blocks`) and
  headers-first synchronization; restores `EventualConsensus`; checks that
  the responder answering before the requester's FIN, oversize `get-headers`
  responses (misbehavior points, not a connection error) and early-finished
  `get-blocks` responses are all handled without a protocol error.
- **Phase 3** — v2 download scheduler, the part of the draft Zebra has not
  implemented yet: `REFUSED`, early finish, `CANCELLED` and silent timeout
  must never be recorded as not-found (the v1 stall bug, zebra#10679, with
  more ways to not receive a block).
- **Phase 4** — misbehavior and banning: honest peers on divergent chains
  never ban each other.
