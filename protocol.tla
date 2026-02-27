---- MODULE protocol ----
(* https://zips.z.cash/zip-0204 *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT InitialPeers
CONSTANT MaxBlock
CONSTANT MaxRounds

VARIABLES p2p_network, round, done
VARIABLES clock, last_recv_at
VARIABLE blockchains

----
vars == << p2p_network, round, done, clock, last_recv_at, blockchains >>

ClockConstraint == clock <= 10

\* For each initial peer construct a set of all other peers. 
OtherPeers == [ n \in InitialPeers |-> InitialPeers \ { n } ]

----
Init == 
    /\ p2p_network = [ i \in InitialPeers |-> [ j \in OtherPeers[i] |-> <<>> ] ]
    /\ round = 0
    /\ done = FALSE
    /\ clock = 0
    \* this ones can probably just go inside the p2p_network variable?
    /\ last_recv_at = [i \in InitialPeers |-> [ j \in OtherPeers[i] |-> 0 ]]
    /\ \E blockset \in [ InitialPeers -> (1..MaxBlock) ] :
        blockchains = [ i \in InitialPeers |-> [ blocks |-> 1..blockset[i] ] ]

VersionMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) = 0
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
                            start_height |-> Cardinality(blockchains[n].blocks),
                            relay |-> FALSE
                        ]
                    ]
                    base == p2p_network[n][m] IN
                /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, version) ]
                /\ UNCHANGED << last_recv_at, blockchains, clock >>

VerackMsg ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) >= 1
            /\ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "version"
            /\ LET
                    verack == [
                        header |-> [
                             magic |-> 619259748,
                             command |-> "verack",
                             length |-> 0,
                             checksum |-> 0
                         ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, verack) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
            /\ UNCHANGED << blockchains, clock >>

PingMessage == 
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ last_recv_at[n][m] >= clock - 3
            /\ LET
                    ping == [header |-> [
                        magic |-> 619259748,
                        command |-> "ping",
                        length |-> 0,
                        checksum |-> 0
                    ]]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, ping) ]
            /\ UNCHANGED << last_recv_at, clock, blockchains >>

PongMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) > 0
            /\ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "ping"
            /\ LET
                    pong == [
                        header |-> [
                             magic |-> 619259748,
                             command |-> "pong",
                             length |-> 0,
                             checksum |-> 0
                         ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, pong) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
            /\ UNCHANGED << clock, blockchains >>

InvMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) >= 2
            /\ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "verack"
            /\ p2p_network[n][m][Len(p2p_network[n][m]) - 1].header.command = "version"
            /\ blockchains[n].blocks # {}
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
                            inventory |-> << [type |-> "MSG_BLOCK", hash |-> Cardinality(blockchains[n].blocks)] >>
                        ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, inv) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
            /\ UNCHANGED << clock, blockchains >>

GetHeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) >= 3
            /\ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "inv"
            /\ Cardinality(blockchains[n].blocks) < Cardinality(blockchains[m].blocks)
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
                            blockLocatorHashes |-> << Cardinality(blockchains[n].blocks) >>,
                            hashStop |-> 0
                        ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, getheaders) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
                    
            /\ UNCHANGED << clock, blockchains >>

HeadersMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) >= 4
            /\ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "getheaders"
            /\ Cardinality(blockchains[n].blocks) < Cardinality(blockchains[m].blocks)
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
                            headers |-> << [version |-> 70015, prev_block |-> Cardinality(blockchains[n].blocks), merkle_root |-> 0, timestamp |-> clock, bits |-> 0, nonce |-> 0] >>
                        ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, headers) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
            /\ UNCHANGED << clock, blockchains >>

GetDataMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) >= 5
            /\ \/ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "headers"
               \/ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "block"
            /\ Cardinality(blockchains[n].blocks) < Cardinality(blockchains[m].blocks)
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
                            inventory |-> << [type |-> "MSG_BLOCK", hash |-> Cardinality(blockchains[n].blocks)] >>
                        ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, getdata) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
            /\ UNCHANGED << clock, blockchains >>

BlockMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(p2p_network[n][m]) >= 6
            /\ p2p_network[n][m][Len(p2p_network[n][m])].header.command = "getdata"
            /\ Cardinality(blockchains[n].blocks) < Cardinality(blockchains[m].blocks)
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
                            prev_block |-> Cardinality(blockchains[n].blocks),
                            merkle_root |-> 0,
                            timestamp |-> clock,
                            bits |-> 0,
                            nonce |-> 0,
                            transactions |-> << >>
                        ]
                    ]
                    base == p2p_network[n][m] 
                IN
                    /\ p2p_network' = [ p2p_network EXCEPT ![n][m] = Append(base, block) ]
                    /\ last_recv_at' = [last_recv_at EXCEPT ![n][m] = clock]
                    /\ blockchains' = [ blockchains EXCEPT ![n].blocks = blockchains[n].blocks \cup {Cardinality(blockchains[n].blocks) + 1} ]
                    /\ IF \A i, j \in InitialPeers : blockchains'[i].blocks = blockchains'[j].blocks
                        THEN PrintT(<<"ALL PEERS SYNCED", blockchains'>>)
                        ELSE TRUE
            /\ UNCHANGED << clock >>

Tick ==
    /\ ~done
    /\ clock' = clock + 1
    /\ UNCHANGED << last_recv_at, p2p_network, round, done, blockchains >>

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
    /\ UNCHANGED << p2p_network, round, clock, last_recv_at, blockchains >>

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