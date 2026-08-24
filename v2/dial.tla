---- MODULE dial ----
(*
Simultaneous-dial specification for the version 2 connection layer.

The draft's whole rule for duplicate connections is one sentence
("Connection Management"): "A node SHOULD maintain at most one connection to
a given remote address." It says nothing about the simultaneous-open race —
two nodes dialling each other at once, so that two connections exist before
either side can see the duplicate — nor which of the two connections a node
should keep. This module checks what each way of filling that gap does.

Two peers each want a connection to the other. There are two possible
connections, named by their dialer. Each side sees a connection's state only
locally; opens and closes propagate asynchronously, so a node can accept an
inbound connection while its own outbound dial is still unanswered — the
race. A node that observes a duplicate at accept time applies one policy:

  "prefer_outbound"  refuse the inbound duplicate, keep the own dial.
                     Locally this is also "keep the first connection": the
                     node's own dial always precedes the accept, or the
                     dial would have been blocked.
  "prefer_inbound"   accept the inbound duplicate, close the own dial.
  "tiebreak"         keep the connection dialled by the fixed Lower peer,
                     whichever side of it this node is on — the one
                     asymmetric convention.

Both symmetric policies are self-defeating when applied by both peers: each
node keeps the connection the other node closes, so both connections die and
both nodes redial — forever, under adversarial timing. The liveness property
EventuallyOneConnection is violated. Only the asymmetric tie-break makes the
peers agree on a survivor, and with it the property holds.

The model assumes the best case for the draft: each node can even RECOGNIZE
the inbound duplicate (in practice an inbound connection arrives from an
ephemeral UDP port, not the remote's canonical listen address, so matching
it to an outbound dial already needs an address-book lookup by IP). The gap
exists even in this best case.

See ../documents/v2-modeling.md for the full write-up.
*)
EXTENDS Naturals, FiniteSets

CONSTANT Peers    \* exactly two peers, each wanting a connection to the other
CONSTANT Lower    \* the peer whose dial survives under the tie-break policy
CONSTANT Policy   \* "prefer_outbound" | "prefer_inbound" | "tiebreak"

ASSUME Cardinality(Peers) = 2
ASSUME Lower \in Peers
ASSUME Policy \in { "prefer_outbound", "prefer_inbound", "tiebreak" }

Other(p) == CHOOSE q \in Peers : q # p

\* One record per possible connection, named by its dialer i:
\*   d      the dialer's local state of it
\*   a      the acceptor's local state of it
\*   syn    the open is in flight toward the acceptor
\*   fin_d  a close notice is in flight toward the dialer
\*   fin_a  a close notice is in flight toward the acceptor
ConnState == { "none", "open", "closed" }

VARIABLE conns   \* [ Peers -> [ d, a : ConnState, syn, fin_d, fin_a : BOOLEAN ] ]

vars == << conns >>

NullConn == [ d |-> "none", a |-> "none",
              syn |-> FALSE, fin_d |-> FALSE, fin_a |-> FALSE ]

\* p's local view: the connections p currently considers open. p is the
\* dialer of conns[p] and the acceptor of the other connection.
ViewOpen(p) == { i \in Peers : IF i = p THEN conns[i].d = "open"
                                        ELSE conns[i].a = "open" }

----

Init == conns = [ i \in Peers |-> NullConn ]

\* p dials its peer: only when p sees no connection to it, open or its own
\* earlier dial ("at most one connection to a given remote address").
Dial ==
    \E p \in Peers:
        /\ conns[p].d = "none"
        /\ ViewOpen(p) = {}
        /\ conns' = [ conns EXCEPT ![p].d = "open", ![p].syn = TRUE ]

\* The acceptor q of connection i observes the incoming open. If q's own dial
\* is still open from its point of view, this is the simultaneous-open race
\* and the policy decides which connection survives; otherwise q accepts.
\* Refusing sets the acceptor side closed and sends a close notice to the
\* dialer; preferring the inbound also closes q's own dial.
AcceptConn(i) ==
        LET q == Other(i)
            dup == conns[q].d = "open"
            keepInbound == \/ Policy = "prefer_inbound"
                           \/ Policy = "tiebreak" /\ i = Lower
        IN
        /\ conns[i].syn
        /\ conns[i].a = "none"
        /\ \/ /\ ~dup
              /\ conns' = [ conns EXCEPT ![i].a = "open", ![i].syn = FALSE ]
           \/ /\ dup
              /\ \/ /\ keepInbound
                    /\ conns' = [ conns EXCEPT
                            ![i].a = "open",  ![i].syn = FALSE,
                            ![q].d = "closed", ![q].fin_a = TRUE ]
                 \/ /\ ~keepInbound
                    /\ conns' = [ conns EXCEPT
                            ![i].a = "closed", ![i].syn = FALSE,
                            ![i].fin_d = TRUE ]

Accept == \E i \in Peers: AcceptConn(i)

\* A side observes the peer's close notice and closes its own side.
RecvFinD(i) ==
    /\ conns[i].fin_d
    /\ conns' = [ conns EXCEPT ![i].d = IF @ = "open" THEN "closed" ELSE @,
                               ![i].fin_d = FALSE ]

RecvFinA(i) ==
    /\ conns[i].fin_a
    /\ conns' = [ conns EXCEPT ![i].a = IF @ = "open" THEN "closed" ELSE @,
                               ![i].fin_a = FALSE ]

RecvFin == \E i \in Peers: RecvFinD(i) \/ RecvFinA(i)

\* A connection both of whose sides are done, with nothing in flight, resets
\* so the dialer may try again.
SettleConn(i) ==
    /\ conns[i].d = "closed"
    /\ conns[i].a \in { "closed", "none" }
    /\ ~conns[i].syn /\ ~conns[i].fin_d /\ ~conns[i].fin_a
    /\ conns' = [ conns EXCEPT ![i] = NullConn ]

Settle == \E i \in Peers: SettleConn(i)

----

Next == Dial \/ Accept \/ RecvFin \/ Settle

\* Fairness is per connection: each specific incoming open, close notice
\* and settle is eventually processed, and disconnected nodes keep
\* redialling. Existential fairness over all connections would let one
\* peer's endless redial cycle discharge the obligation while the other
\* connection's accept starves — a scheduler artifact, not a policy
\* behaviour. The flap under a symmetric policy contains every one of these
\* actions infinitely often, so it remains a fair counterexample.
Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Dial)
    /\ \A i \in Peers :
           /\ WF_vars(AcceptConn(i))
           /\ WF_vars(RecvFinD(i))
           /\ WF_vars(RecvFinA(i))
           /\ WF_vars(SettleConn(i))

----

\* A connection fully established on both sides, with nothing else alive.
Stable ==
    \E i \in Peers:
        /\ conns[i].d = "open" /\ conns[i].a = "open" /\ ~conns[i].syn
        /\ conns[Other(i)] = NullConn

\* Liveness: the pair eventually settles on exactly one connection and keeps
\* it. Violated by both symmetric policies (perpetual flap); holds under the
\* asymmetric tie-break.
EventuallyOneConnection == <>[] Stable

----
\* Safety invariants.

TypeOK ==
    conns \in [ Peers -> [ d : ConnState, a : ConnState,
                           syn : BOOLEAN, fin_d : BOOLEAN, fin_a : BOOLEAN ] ]

\* No node ever considers two connections to the same peer open at once —
\* every policy enforces the draft's "at most one" locally. The flap is not
\* a violation of the stated rule; it lives entirely in the gap the rule
\* leaves open.
AtMostOnePerView ==
    \A p \in Peers : Cardinality(ViewOpen(p)) <= 1

====
