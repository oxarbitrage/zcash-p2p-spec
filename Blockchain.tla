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
====
