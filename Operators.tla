---- MODULE Operators ----
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Utils
VARIABLE the_network

\* Given a block collection and a hash, returns the block with the given hash.
FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash

\* Updates the blocks of a peer in the network.
UpdatePeerBlocks(peer_address, new_blocks) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = peer_address THEN
        [the_network[i] EXCEPT !.blocks = @ \cup {new_blocks}]
    ELSE
        the_network[i]
]

\* Update the peer set of a local peer with a new remote peer address establishing a connection.
UpdatePeerSet(local_peer_address, remote_peer_address) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = local_peer_address THEN
        [the_network[i] EXCEPT !.peer_set = @ \cup {remote_peer_address}]
    ELSE
        the_network[i]
]

\* Update the chain tip of a peer in the network.
UpdatePeerTip(peer_address, new_tip) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = peer_address THEN
        [the_network[i] EXCEPT !.chain_tip = new_tip]
    ELSE
        the_network[i]
]

\* Given a block collection, a start height and an end height, returns the blocks in the given range.
FindBlocks(block_collection, start_height, end_height) == 
    { r \in DOMAIN [b \in block_collection |-> b.height >= start_height /\ b.height <= end_height] : TRUE }

\* Get the peer a peer from the network given a peer address.
GetPeerFromNetwork(peer_address) == CHOOSE peer \in ToSet(the_network) : peer.peer = peer_address

\* Get the chain tip of a peer given a peer address.
GetPeerTip(peer_address) == (CHOOSE peer \in ToSet(the_network) : peer.peer = peer_address).chain_tip.height

\* Get the blocks of a peer given a peer address.
GetPeerBlocks(peer_address) == (CHOOSE peer \in ToSet(the_network) : peer.peer = peer_address).blocks

====
