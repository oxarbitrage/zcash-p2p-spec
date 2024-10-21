---- MODULE Blockchain ----

EXTENDS Integers, Sequences, TLC, Utils

(* Create a network of peers with the given number of peers, block counts for each of them,
and connections to be established. *)
CreateNetwork(numPeers, blockCounts, connections) ==
    [peer \in 1..numPeers |->
        LET numBlocks == blockCounts[peer]
            lastBlockHash == IF numBlocks > 0
                THEN "blockhash" \o ToString(numBlocks)
            ELSE "blockhash0"
            \* Construct peer_set as a sequence of other peers, seeder nodes have no connections.
            peerSet == IF connections[peer] = TRUE THEN
                Remove(
                    \* Add all peers to the list.
                    [ i \in 1..numPeers |-> [
                        address |-> "peer" \o ToString(i),
                        tip |-> blockCounts[i],
                        established |-> FALSE
                    ]],
                    \* Remove the current peer from the list.
                    [
                        address |-> "peer" \o ToString(peer),
                        tip |-> blockCounts[peer],
                        established |-> FALSE
                    ])
            ELSE <<>>
        IN [
            peer |-> "peer" \o ToString(peer),
            blocks |-> ToSet([height \in 1..numBlocks |-> [
                height |-> height,
                hash |-> "blockhash" \o ToString(height),
                block |-> "serialized block data " \o ToString(height)
            ]]),
            peer_set |-> peerSet,
            chain_tip |-> [height |-> numBlocks, hash |-> lastBlockHash]
        ]
    ]

(*
    - 2 peers.
    - 1 seeder with 1 block and no outbound connections.
    - 1 peer with no blocks and an outbound connection to the seeder.
*)
Blockchain1 == CreateNetwork(2, <<1, 0>>, <<FALSE, TRUE>>)

(*
    - 2 peers.
    - 1 seeder with 10 block and no outbound connections.
    - 1 peer with no blocks and an outbound connection to the seeder.
*)
Blockchain2 == CreateNetwork(2, <<10, 0>>, <<FALSE, TRUE>>)

(*
    - 3 peers.
    - 1 seeder with 1 block and no outbound connections.
    - 1 peer with no blocks and an outbound connection to the seeder.
    - 1 peer with no blocks and an outbound connection to the seeder.
*)
Blockchain3 == CreateNetwork(3, <<1, 0, 0>>, <<FALSE, TRUE, TRUE>>)

====
