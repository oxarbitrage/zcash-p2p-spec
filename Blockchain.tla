---- MODULE Blockchain ----

\* A simple blockchain model. *\
PEERS == {
    [peer |-> "peer1", blocks |-> {
        [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
        [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
        [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
        [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"],
        [height |-> 5, hash |-> "blockhash5", block |-> "serialized block data 5"]
    }, peer_set |-> {}, chain_tip |-> [height|-> 5, hash |-> "blockhash5"]
    ],
    [peer |-> "peer2",
        blocks |-> {}, \* No blocks.
        peer_set |-> {}, \* No connections.
        chain_tip |-> [height|-> 0, hash |-> "blockhash0"] \* No blocks.
    ]
    \*,
    \*[peer |-> "peer3",
    \*    blocks |-> {}, \* No blocks.
    \*    peer_set |-> {}, \* No connections.
    \*    chain_tip |-> 0 \* No blocks.
    \*]
}

====

EXTENDS Naturals, Sequences

====