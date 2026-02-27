---- MODULE protocol ----
(* https://zips.z.cash/zip-0204 *)

EXTENDS TLC, Naturals, Sequences, FiniteSets, messages

CONSTANT InitialPeers
CONSTANT MaxBlock

VARIABLES nodes, clock

----
vars == << nodes, clock >>

\* For each initial peer construct a set of all other peers. 
OtherPeers == [ n \in InitialPeers |-> InitialPeers \ { n } ]

----
Init == 
    /\ clock = 0
    /\ \E blockset \in [ InitialPeers -> (1..MaxBlock) ] :
        nodes = [ i \in InitialPeers |-> [
            channels     |-> [ j \in OtherPeers[i] |-> <<>> ],
            last_recv_at |-> [ j \in OtherPeers[i] |-> 0 ],
            blocks       |-> 1..blockset[i]
        ]]

VersionMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) = 0
            /\ nodes' = [ nodes EXCEPT ![n].channels[m] = Append(@, MakeVersion(n, m, clock, nodes[n].blocks)) ]
            /\ UNCHANGED << clock >>

VerackMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 1
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "version"
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeVerack),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

PingMessage == 
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].last_recv_at[m] <= clock - 3
            /\ nodes' = [ nodes EXCEPT ![n].channels[m] = Append(@, MakePing) ]
            /\ UNCHANGED << clock >>

PongMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) > 0
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "ping"
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakePong),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

InvMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 2
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "verack"
            /\ nodes[n].channels[m][Len(nodes[n].channels[m]) - 1].header.command = "version"
            /\ nodes[n].blocks # {}
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeInv(nodes[n].blocks)),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

GetHeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 3
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "inv"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeGetHeaders(nodes[n].blocks)),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

HeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 4
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "getheaders"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeHeaders(nodes[n].blocks, clock)),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

GetDataMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 5
            /\ \/ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "headers"
               \/ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "block"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeGetData(nodes[n].blocks)),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

BlockMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 6
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "getdata"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ nodes' = [ nodes EXCEPT
                    ![n].channels[m]     = Append(@, MakeBlock(nodes[n].blocks, clock)),
                    ![n].last_recv_at[m] = clock,
                    ![n].blocks          = nodes[n].blocks \cup {Cardinality(nodes[n].blocks) + 1} ]
            
            /\ UNCHANGED << clock >>

Tick ==
    /\ clock < 10
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

Spec == 
    Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)

AllSynced == <> \A i, j \in InitialPeers : nodes[i].blocks = nodes[j].blocks

====
