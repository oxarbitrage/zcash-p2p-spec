---- MODULE refinement ----
(*
protocol.tla refines the downloader abstraction, one pipeline per peer.

The mapping forgets streams, handshakes and announcements: a peer's
verified set is its block set, and its in-flight set is every height named
in a get-blocks request record still queued toward a responder or in a
blocks response record still queued back. Opening a request maps to
Request; consuming a response to Deliver; a connection close that wipes an
outstanding request to Requeue; mining to Extend; everything else — the
handshake, announcements, headers, the serve step (which moves a height
from the request record to the response record without leaving flight) —
stutters.

Checked with MaxBlocksPerRequest = 1 so that one concrete step carries one
abstract Request/Deliver; a batch of two would be two abstract steps in
one, which the abstraction (deliberately minimal) does not allow.
*)
EXTENDS protocol

SeqToSet(q) == { q[i] : i \in 1..Len(q) }

\* Heights named by a queued record, for the two record kinds that carry
\* blocks in flight.
RecHeights(x) == IF x.kind \in { "get-blocks", "blocks" } THEN SeqToSet(x.heights) ELSE {}

QueueHeights(q) == UNION { RecHeights(q[i]) : i \in 1..Len(q) }

\* Blocks peer n currently has in flight: heights in its request records
\* still queued toward some responder, plus heights in response records
\* still queued back to n on its own request streams.
DlInflight(n) ==
    UNION { UNION { QueueHeights(S(m, n, sid).inq) \cup QueueHeights(S(n, m, sid).inq)
                    : sid \in { s \in StreamIds(n, m) : s[1] = n } }
            : m \in OtherPeers[n] }

DlVerified(n) == nodes[n].blocks

D(n) == INSTANCE downloader WITH verified <- DlVerified(n),
                                 inflight <- DlInflight(n),
                                 MaxBlock <- MaxBlock

MappedVars(n) == << DlVerified(n), DlInflight(n) >>

\* TLC checks specification properties in implied-init / implied-action
\* form; a quantified D(n)!Spec is not accepted directly, so the same
\* formula is stated as one: every peer's mapped state satisfies the
\* abstract Init, and every step is an abstract step or a stutter of every
\* peer's mapped state.
RefinesDownloader ==
    /\ \A n \in InitialPeers : D(n)!Init
    /\ [][ \A n \in InitialPeers : [D(n)!Next]_(MappedVars(n)) ]_vars

====
