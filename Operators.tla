---- MODULE Operators ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Utils
VARIABLE the_network

\* Given a block collection and a hash, returns the block with the given hash.
FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash

\* Update the peer set of a local peer with a new remote peer address establishing a connection.
UpdatePeerSet(local_peer_address, remote_peer_address) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = local_peer_address THEN
        [the_network[i] EXCEPT !.peer_set = @ \cup {remote_peer_address}]
    ELSE
        the_network[i]
]

\* Given a block collection, a start height and an end height, returns the blocks in the given range.

FindBlocks(block_collection, start_height, end_height) == 
    { b \in block_collection :
        /\ b.height >= start_height
        /\ b.height <= end_height
    }

\* Get the peer a peer from the network given a peer address.
GetPeerFromNetwork(peer_address) == CHOOSE peer \in ToSet(the_network) : peer.peer = peer_address

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Get the chain tip of a peer given a peer address.
GetPeerTipByAddress(peer_address) ==
    LET peer_blocks == (CHOOSE peer \in ToSet(the_network) : peer.peer = peer_address).blocks
    IN IF peer_blocks = {} THEN
        [height |-> 0, block |-> "serialized block data 0", hash |-> "blockhash 0"]
    ELSE
        CHOOSE block \in peer_blocks : block.height = Max({b.height : b \in peer_blocks})

\* Get the chain tip of a peer given a peer index in the network.
GetPeerTipByIndex(peer_index) ==
    IF the_network[peer_index].blocks = {} THEN
        [height |-> 0, block |-> "serialized block data 0", hash |-> "blockhash 0"]
    ELSE
        CHOOSE block \in the_network[peer_index].blocks : block.height =
            Max({b.height : b \in the_network[peer_index].blocks})

\* Get the chain tip of a peer given a peer index in the network.
GetPeerTipByIndexAndNetwork(peer_index, network) ==
    IF network[peer_index].blocks = {} THEN
        [height |-> 0, block |-> "serialized block data 0", hash |-> "blockhash 0"]
    ELSE
        CHOOSE block \in network[peer_index].blocks : block.height =
            Max({b.height : b \in network[peer_index].blocks})

\* Get the blocks of a peer given a peer address.
GetPeerBlocks(peer_address) == (CHOOSE peer \in ToSet(the_network) : peer.peer = peer_address).blocks

====
