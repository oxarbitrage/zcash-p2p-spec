---- MODULE Blockchain ----

\* A simple blockchain model. *\
PEERS == <<
    [peer |-> "peer1", blocks |-> {
        [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
        [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
        [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
        [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"],
        [height |-> 5, hash |-> "blockhash5", block |-> "serialized block data 5"],
        [height |-> 6, hash |-> "blockhash6", block |-> "serialized block data 6"]
    }, peer_set |-> <<>>, chain_tip |-> [height|-> 6, hash |-> "blockhash6"]
    ],
    [peer |-> "peer2",
        blocks |-> {}, \* No blocks.
        peer_set |-> <<[address |-> "peer1", tip |-> 0, established |-> FALSE], [address |-> "peer3", tip |-> 0, established |-> FALSE]>>,
        chain_tip |-> [height|-> 0, hash |-> "blockhash0"] \* No blocks.
    ],
    [peer |-> "peer3",
        blocks |-> {
            [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
            [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
            [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
            [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"],
            [height |-> 5, hash |-> "blockhash5", block |-> "serialized block data 5"],
            [height |-> 6, hash |-> "blockhash6", block |-> "serialized block data 6"]

        }, \* Almost all blocks.
        peer_set |-> <<>>,
        chain_tip |-> [height|-> 6, hash |-> "blockhash6"]
    ],
    [peer |-> "peer4",
        blocks |-> {}, \* No blocks.
        peer_set |-> <<>>,
        chain_tip |-> [height|-> 0, hash |-> "blockhash0"]
    ]
>>

====

EXTENDS Naturals, Sequences

====