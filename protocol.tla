---- MODULE protocol ----
(* https://zips.z.cash/zip-0204 *)

EXTENDS TLC, Naturals, Sequences, FiniteSets, messages

CONSTANT InitialPeers
CONSTANT MaxBlock
CONSTANT MaxClock
CONSTANT DisconnectTimeout

VARIABLES nodes, clock

----
vars == << nodes, clock >>

\* See README for an explanation of symmetry reduction.
Symmetry == Permutations(InitialPeers)

\* For each initial peer construct a set of all other peers.
OtherPeers == [ n \in InitialPeers |-> InitialPeers \ { n } ]

----
Init == 
    /\ clock = 0
    /\ \E blockset \in [ InitialPeers -> (1..MaxBlock) ] :
        nodes = [ i \in InitialPeers |-> [
            channels     |-> [ j \in OtherPeers[i] |-> <<>> ],
            conn         |-> [ j \in OtherPeers[i] |-> "init" ],
            ping_nonce   |-> [ j \in OtherPeers[i] |-> 0 ],
            last_recv_at |-> [ j \in OtherPeers[i] |-> 0 ],
            blocks       |-> 1..blockset[i]
        ]]

VersionMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "init"
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m] = Append(@, MakeVersion(n, m, clock, nodes[n].blocks)),
                    ![n].conn[m]     = "version_sent" ]
            /\ UNCHANGED << clock >>

VerackMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "version_sent"
            /\ nodes[m].conn[n] \notin {"init"}  \* m has sent its version
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeVerack),
                    ![n].conn[m]         = "established",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* Models version validation failure: version too old or self-connection nonce match.
\* Non-deterministic: TLC explores both the accept (VerackMsg) and reject paths,
\* verifying that AllSynced holds even when handshakes fail and peers must retry.
RejectMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "version_sent"
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeReject("version")),
                    ![n].conn[m]         = "init",
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

PingMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init", "version_sent"}
            /\ nodes[n].last_recv_at[m] <= clock - 3
            /\ nodes[n].ping_nonce[m] = 0
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]   = Append(@, MakePing(clock)),
                    ![n].ping_nonce[m] = clock ]
            /\ UNCHANGED << clock >>

PongMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].ping_nonce[m] # 0
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakePong(nodes[n].ping_nonce[m])),
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

InvMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "established"
            /\ nodes[n].blocks # {}
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeInv(nodes[n].blocks)),
                    ![n].conn[m]         = "inv_sent",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

GetHeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "inv_sent"
            /\ \/ /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
                  /\ nodes' = [ nodes EXCEPT
                          ![n].channels[m]     = Append(@, MakeGetHeaders(nodes[n].blocks)),
                          ![n].conn[m]         = "getheaders_sent",
                          ![n].last_recv_at[m] = clock ]
               \/ /\ Cardinality(nodes[n].blocks) >= Cardinality(nodes[m].blocks)
                  /\ nodes' = [ nodes EXCEPT ![n].conn[m] = "synced" ]
            /\ UNCHANGED << clock >>

HeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "getheaders_sent"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeHeaders(nodes[n].blocks, clock)),
                    ![n].conn[m]         = "headers_sent",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

GetDataMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \in {"headers_sent", "block_received"}
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeGetData(nodes[n].blocks)),
                    ![n].conn[m]         = "getdata_sent",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

BlockMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "getdata_sent"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ LET newBlocks == nodes[n].blocks \cup {Cardinality(nodes[n].blocks) + 1}
               IN nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeBlock(nodes[n].blocks, clock)),
                    ![n].last_recv_at[m] = clock,
                    ![n].blocks          = newBlocks,
                    ![n].conn[m]         = IF Cardinality(newBlocks) < Cardinality(nodes[m].blocks)
                                           THEN "block_received"
                                           ELSE "synced" ]
            /\ IF \A i, j \in InitialPeers : nodes'[i].blocks = nodes'[j].blocks
                THEN PrintT(<<"ALL PEERS SYNCED at clock", clock>>)
                ELSE TRUE
            /\ UNCHANGED << clock >>

Disconnect ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init"}
            /\ clock - nodes[n].last_recv_at[m] > DisconnectTimeout
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = <<>>,
                    ![n].conn[m]         = "init",
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << nodes >>

Next ==
    \/ Tick
    \/ VersionMsg
    \/ VerackMsg
    \/ PingMessage
    \/ PongMessage
    \/ InvMessage
    \/ GetHeadersMessage
    \/ HeadersMessage
    \/ GetDataMessage
    \/ BlockMessage
    \/ Disconnect
    \/ RejectMsg

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ SF_vars(VerackMsg)

AllSynced == <> \A i, j \in InitialPeers : nodes[i].blocks = nodes[j].blocks

====
