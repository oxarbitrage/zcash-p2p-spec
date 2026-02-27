---- MODULE protocol ----
(* https://zips.z.cash/zip-0204 *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT InitialPeers
CONSTANT MaxBlock
CONSTANT MaxRounds

VARIABLES nodes, round, done, clock

----
vars == << nodes, round, done, clock >>

ClockConstraint == clock <= 10

\* For each initial peer construct a set of all other peers. 
OtherPeers == [ n \in InitialPeers |-> InitialPeers \ { n } ]

----
Init == 
    /\ round = 0
    /\ done = FALSE
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
            /\ 
                LET
                    version == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "version",
                            length |-> 0,
                            checksum |-> 0
                        ],
                        payload |-> [
                            version |-> 70015,
                            services |-> 0,
                            timestamp |-> clock,
                            addr_recv |-> m,
                            addr_from |-> n,
                            nonce |-> 0,
                            user_agent |-> "",
                            start_height |-> Cardinality(nodes[n].blocks),
                            relay |-> FALSE
                        ]
                    ]
                    base == nodes[n].channels[m] IN
                /\ nodes' = [ nodes EXCEPT ![n].channels[m] = Append(base, version) ]
                /\ UNCHANGED << clock >>

VerackMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 1
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "version"
            /\ LET
                    verack == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "verack",
                            length |-> 0,
                            checksum |-> 0
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, verack),
                            ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

PingMessage == 
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].last_recv_at[m] <= clock - 3
            /\ LET
                    ping == [header |-> [
                        magic |-> 619259748,
                        command |-> "ping",
                        length |-> 0,
                        checksum |-> 0
                    ]]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT ![n].channels[m] = Append(base, ping) ]
            /\ UNCHANGED << clock >>

PongMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) > 0
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "ping"
            /\ LET
                    pong == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "pong",
                            length |-> 0,
                            checksum |-> 0
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, pong),
                            ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

InvMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 2
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "verack"
            /\ nodes[n].channels[m][Len(nodes[n].channels[m]) - 1].header.command = "version"
            /\ nodes[n].blocks # {}
            /\ LET
                    inv == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "inv",
                            length |-> 0,
                            checksum |-> 0
                        ],
                        payload |-> [
                            count |-> 1,
                            inventory |-> << [type |-> "MSG_BLOCK", hash |-> Cardinality(nodes[n].blocks)] >>
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, inv),
                            ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

GetHeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 3
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "inv"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ LET
                    getheaders == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "getheaders",
                            length |-> 0,
                            checksum |-> 0
                        ],
                        payload |-> [
                            version |-> 70015,
                            hashCount |-> 1,
                            blockLocatorHashes |-> << Cardinality(nodes[n].blocks) >>,
                            hashStop |-> 0
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, getheaders),
                            ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

HeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 4
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "getheaders"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ LET
                    headers == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "headers",
                            length |-> 0,
                            checksum |-> 0
                        ],
                        payload |-> [
                            count |-> 1,
                            headers |-> << [version |-> 70015, prev_block |-> Cardinality(nodes[n].blocks), merkle_root |-> 0, timestamp |-> clock, bits |-> 0, nonce |-> 0] >>
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, headers),
                            ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

GetDataMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 5
            /\ \/ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "headers"
               \/ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "block"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ LET
                    getdata == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "getdata",
                            length |-> 0,
                            checksum |-> 0
                        ],
                        payload |-> [
                            count |-> 1,
                            inventory |-> << [type |-> "MSG_BLOCK", hash |-> Cardinality(nodes[n].blocks)] >>
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, getdata),
                            ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

BlockMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].channels[m]) >= 6
            /\ nodes[n].channels[m][Len(nodes[n].channels[m])].header.command = "getdata"
            /\ Cardinality(nodes[n].blocks) < Cardinality(nodes[m].blocks)
            /\ LET
                    block == [
                        header |-> [
                            magic |-> 619259748,
                            command |-> "block",
                            length |-> 0,
                            checksum |-> 0
                        ],
                        payload |-> [
                            version |-> 70015,
                            prev_block |-> Cardinality(nodes[n].blocks),
                            merkle_root |-> 0,
                            timestamp |-> clock,
                            bits |-> 0,
                            nonce |-> 0,
                            transactions |-> << >>
                        ]
                    ]
                    base == nodes[n].channels[m] 
                IN
                    /\ nodes' = [ nodes EXCEPT
                            ![n].channels[m] = Append(base, block),
                            ![n].last_recv_at[m] = clock,
                            ![n].blocks = nodes[n].blocks \cup {Cardinality(nodes[n].blocks) + 1} ]
                    /\ IF \A i, j \in InitialPeers : nodes'[i].blocks = nodes'[j].blocks
                        THEN PrintT(<<"ALL PEERS SYNCED", nodes'>>)
                        ELSE TRUE
            /\ UNCHANGED << clock >>

Tick ==
    /\ ~done
    /\ clock' = clock + 1
    /\ UNCHANGED << nodes, round, done >>

DoRound ==
    /\ ~done
    /\ round < MaxRounds
    /\ (\/ VersionMsg
        \/ VerackMsg
        \/ PingMessage
        \/ PongMessage
        \/ InvMessage
        \/ GetHeadersMessage
        \/ HeadersMessage
        \/ GetDataMessage
        \/ BlockMessage)
    /\ round' = round + 1
    /\ UNCHANGED << done, clock >>

Done ==
    /\ ~done
    /\ round = MaxRounds
    /\ done' = TRUE
    /\ UNCHANGED << nodes, round, clock >>

Stutter ==
    /\ done
    /\ UNCHANGED vars

Next ==
    IF done THEN
        Stutter
    ELSE
        \/ Tick
        \/ DoRound
        \/ Done

Spec == 
    Init 
    /\ [][Next]_vars

====
