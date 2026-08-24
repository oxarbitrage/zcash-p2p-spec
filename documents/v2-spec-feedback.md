# Draft feedback for zcash/zips#1344 from the TLA+ model

Against draft revision `a3f4fa2a`. Each item has a reproducible TLC trace in
this repository (`v2/`). Wording proposals are suggestions only.

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
