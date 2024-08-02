---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils

MaxGetBlocksInvResponse == 3

MAX_PEERS == 2

IDENTIFIER_DIFFERENCE_OF_PROCESSES == 1000

PEER1 == [peer |-> "peer1", blocks |-> {
            [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
            [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
            [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
            [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"]
        }, peer_set |-> {}, chain_tip |-> 4]

PEER2 == [
            peer |-> "peer2",
            blocks |-> {}, \* No blocks.
            peer_set |-> {}, \* No connections.
            chain_tip |-> 0 \* No blocks.
        ]

PEER3 == [
            peer |-> "peer3",
            blocks |-> {}, \* No blocks.
            peer_set |-> {}, \* No connections.
            chain_tip |-> 0 \* No blocks.
        ]

(*--algorithm p2p

variables
    the_network = <<>>;
    selected_remote_peer = defaultInitValue;
    message_header = <<defaultInitValue, defaultInitValue, defaultInitValue>>;
    message_payload = <<defaultInitValue, defaultInitValue, defaultInitValue>>;
define
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
        [b \in block_collection |-> b.height >= start_height /\ b.height <= end_height]

    \* Get the peer set of a peer given a peer address and the network state as a set.
    GetPeerFromNetwork(state, peer_address) == CHOOSE rec \in state : rec.peer = peer_address
end define;

\* Create a connection between the remote and local peer.
procedure create_connection(remote_peer_addr, local_peer_addr)
begin
    VersionMessage:
        \* Version messages are sent from the remote transmitting node to the local receiver node:
        \* > The "version" message provides information about the transmitting node to the receiving node
        \* > at the beginning of a connection."
        \* https://developer.bitcoin.org/reference/p2p_networking.html#version

        \* Create a message header.
        message_header[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] := [
            start_string |-> "f9beb4d9",
            command_name |-> "version",
            payload_size |-> 1,
            checksum |-> "0x5df6e0e2"];
    
        \* Create a version message from local_peer_addr requesting connection with remote_peer_addr
        message_payload[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] := [
            version |-> "70015",
            services |-> "0x01",
            timestamp |-> "",
            addr_recv |-> local_peer_addr,
            addr_trans |-> remote_peer_addr,
            nonce |-> "",
            user_agent |-> "",
            start_height |-> GetPeerFromNetwork(ToSet(the_network), remote_peer_addr).chain_tip,
            relay |-> ""];
    return;
end procedure;

\* Send a verack message to the remote peer.
procedure send_verack()
begin
    VerackMessage:
        message_header[self] := [
            start_string |-> "f9beb4d9",
            command_name |-> "verack", 
            payload_size |-> 0,
            checksum |-> "0x5df6e0e2"];
        message_payload[self] := defaultInitValue;
    return;
end procedure;

\* Look at the peer set of the local node and get one of the peers we are connected to.
procedure get_peer_from_the_network(local_peer_addr)
begin
    GetPeerFromTheNetwork:
        \* The network should have at least 2 peers to make this work.
        await Len(the_network) >= 2;
        \* Get network data of a peer from the local peer set.
        selected_remote_peer := GetPeerFromNetwork(
            ToSet(the_network),
            CHOOSE peer_set \in GetPeerFromNetwork(ToSet(the_network), local_peer_addr).peer_set : TRUE
        );
    return;
end procedure;

\* Request blocks from the selected remote peer by sending a getblocks message.
procedure request_blocks(hashes)
begin
    GetBlocksMessage:
        message_header[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] := [
            start_string |-> "f9beb4d9",
            command_name |-> "getblocks", 
            payload_size |-> 1,
            checksum |-> "0x5df6e0e2"];
        message_payload[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] := [
            version |-> "70015",
            \* TODO: Here we should send the last hash the local peer has.
            hash_count |-> Len(hashes),
            block_header_hashes |-> hashes,
            stop_hash |-> "0"];
    return;
end procedure;

\* Build an inventory message to request blocks from the selected remote peer.
procedure build_inventory_message(found_blocks)
variables blocks, hashes, block_headers;
begin
    ProcessForInventory:
        blocks := { r \in DOMAIN found_blocks : found_blocks[r] = TRUE };
        hashes := SetToSeq({ s.hash : s \in blocks });
        block_headers := [
            h \in 1..Len(hashes) |-> [
                type_identifier |-> "MSG_BLOCK",
                hash |-> hashes[h]
            ]
        ];
    InventoryMessage:
        message_header[self] := [
            start_string |-> "f9beb4d9",
            command_name |-> "inv", 
            payload_size |-> 1,
            checksum |-> "0x5df6e0e2"];

        message_payload[self] := [
            count |-> Len(block_headers),
            inventory |-> block_headers
        ];
    return;
end procedure;

\* Build getdata messages with the inventory received.
procedure process_inventory_message()
begin
    GetDataMessage:
        \* Validate the inventory? For now we just pass it as it came so we just change the global message header.
        message_header[self] := [
            start_string |-> "f9beb4d9",
            command_name |-> "getdata", 
            payload_size |-> message_payload[self].count,
            checksum |-> "0x5df6e0e2"];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure incorporate_data_to_local_peer(local_peer_addr, inventory)
variables c = 1, block_data;
begin
    \* Here we are sure the selected peer has the requested blocks.
    IncorporateLoop:
        while c <= Len(message_payload[self].inventory) do
            block_data := FindBlockByHash(selected_remote_peer.blocks, message_payload[self].inventory[c].hash);
            assert block_data.hash = message_payload[self].inventory[c].hash;
                            
            the_network := UpdatePeerBlocks(local_peer_addr, [
                height |-> block_data.height,
                hash |-> block_data.hash,
                block |-> block_data.block
            ]);        
            c := c + 1;
        end while;
    UpdateTip: the_network := UpdatePeerTip(local_peer_addr, block_data.height);
    return;
end procedure;

\* Peer Client Task
process client_task \in 1..MAX_PEERS
variables remote_peer_addr, local_peer_addr;
begin
    Listening:
        await self > 1;
        await Len(the_network) >= self;
        await Len(message_header) >= self;
        if message_header[self] = defaultInitValue then
            goto Listening;
        end if;
    Requests:
        if message_header[self].command_name = "version" then
            local_peer_addr := message_payload[self].addr_recv;
            remote_peer_addr := message_payload[self].addr_trans;
            call send_verack();
            goto Requests;
        elsif message_header[self].command_name = "verack" then
            \* Add the remote peer to the peer set of the local peer.
            the_network := UpdatePeerSet(local_peer_addr, remote_peer_addr);
        elsif message_header[self].command_name = "getblocks" then
            if message_payload[self].hash_count = 0 then
                \* TODO: This is dirty but correct in some sense, it will build inventory with the 
                \* first `MaxGetBlocksInvResponse` blocks.
                call build_inventory_message(FindBlocks(selected_remote_peer.blocks, 1, 1 + (MaxGetBlocksInvResponse - 1)));
                goto Requests;
            else
                \* TODO: This is wrong, but it build inventory with blocks starting at height 4 and up to 
                \* 4 + `MaxGetBlocksInvResponse`.
                call build_inventory_message(FindBlocks(selected_remote_peer.blocks, 4, 4 + (MaxGetBlocksInvResponse - 1)));
                goto Requests;
            end if;
        elsif message_header[self].command_name = "inv" then
            call process_inventory_message();
            goto Requests;
        elsif message_header[self].command_name = "getdata" then
            call incorporate_data_to_local_peer(local_peer_addr, message_payload[self].inventory);
        end if;
    ClientTaskLoop:
        message_header[self] := defaultInitValue;
        message_payload[self] := defaultInitValue;
        goto Listening;
end process;

process Peer \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS)
variables remote_peer_addr, remote_peer;
begin
    Connect:
        await Len(the_network) = MAX_PEERS;
        local_peer_addr := the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].peer;
        remote_peer_addr := "peer1";

        \* don't do it for the seeder peer.
        await self > (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1);

        call create_connection(remote_peer_addr, local_peer_addr);
    SelectPeerForRequestFromLocalPeer:
        await Len(the_network) = MAX_PEERS /\ Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].peer_set) > 0;
        call get_peer_from_the_network(local_peer_addr);
    RequestInventory:
        await Cardinality(the_network[1].blocks) > 0;
        await Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].blocks) = 0;

        call request_blocks(<<>>);
    RequestMoreBlocks:
        \* Not in sync yet.
        await Cardinality(the_network[1].blocks) = 4;
        await Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].blocks) = 3;

        \* Wait until the messages are empty before requesting more blocks.
        await message_header[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] = defaultInitValue;
        await message_payload[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] = defaultInitValue;

        \* Request more blocks.
        call request_blocks(<<"blockhash4">>);
    CheckSync:
        await Cardinality(the_network[1].blocks) = 4;
        await Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].blocks) = 4;

        await the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].chain_tip = 4;
        print "Network in sync!";
end process;

process Main = 0
begin
    AddPeer:
        the_network := <<PEER1, PEER2>>;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "20339e6d" /\ chksum(tla) = "263bc284")
\* Process variable remote_peer_addr of process client_task at line 212 col 11 changed to remote_peer_addr_
\* Process variable local_peer_addr of process client_task at line 212 col 29 changed to local_peer_addr_
\* Process variable remote_peer_addr of process Peer at line 255 col 11 changed to remote_peer_addr_P
\* Procedure variable hashes of procedure build_inventory_message at line 151 col 19 changed to hashes_
\* Parameter local_peer_addr of procedure create_connection at line 75 col 47 changed to local_peer_addr_c
\* Parameter local_peer_addr of procedure get_peer_from_the_network at line 118 col 37 changed to local_peer_addr_g
CONSTANT defaultInitValue
VARIABLES the_network, selected_remote_peer, message_header, message_payload, 
          pc, stack

(* define statement *)
FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash


UpdatePeerBlocks(peer_address, new_blocks) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = peer_address THEN
        [the_network[i] EXCEPT !.blocks = @ \cup {new_blocks}]
    ELSE
        the_network[i]
]


UpdatePeerSet(local_peer_address, remote_peer_address) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = local_peer_address THEN
        [the_network[i] EXCEPT !.peer_set = @ \cup {remote_peer_address}]
    ELSE
        the_network[i]
]


UpdatePeerTip(peer_address, new_tip) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = peer_address THEN
        [the_network[i] EXCEPT !.chain_tip = new_tip]
    ELSE
        the_network[i]
]


FindBlocks(block_collection, start_height, end_height) ==
    [b \in block_collection |-> b.height >= start_height /\ b.height <= end_height]


GetPeerFromNetwork(state, peer_address) == CHOOSE rec \in state : rec.peer = peer_address

VARIABLES remote_peer_addr, local_peer_addr_c, local_peer_addr_g, hashes, 
          found_blocks, blocks, hashes_, block_headers, local_peer_addr, 
          inventory, c, block_data, remote_peer_addr_, local_peer_addr_, 
          remote_peer_addr_P, remote_peer

vars == << the_network, selected_remote_peer, message_header, message_payload, 
           pc, stack, remote_peer_addr, local_peer_addr_c, local_peer_addr_g, 
           hashes, found_blocks, blocks, hashes_, block_headers, 
           local_peer_addr, inventory, c, block_data, remote_peer_addr_, 
           local_peer_addr_, remote_peer_addr_P, remote_peer >>

ProcSet == (1..MAX_PEERS) \cup ((IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS)) \cup {0}

Init == (* Global variables *)
        /\ the_network = <<>>
        /\ selected_remote_peer = defaultInitValue
        /\ message_header = <<defaultInitValue, defaultInitValue, defaultInitValue>>
        /\ message_payload = <<defaultInitValue, defaultInitValue, defaultInitValue>>
        (* Procedure create_connection *)
        /\ remote_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ local_peer_addr_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_peer_from_the_network *)
        /\ local_peer_addr_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure build_inventory_message *)
        /\ found_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ hashes_ = [ self \in ProcSet |-> defaultInitValue]
        /\ block_headers = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure incorporate_data_to_local_peer *)
        /\ local_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ inventory = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> 1]
        /\ block_data = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_task *)
        /\ remote_peer_addr_ = [self \in 1..MAX_PEERS |-> defaultInitValue]
        /\ local_peer_addr_ = [self \in 1..MAX_PEERS |-> defaultInitValue]
        (* Process Peer *)
        /\ remote_peer_addr_P = [self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) |-> defaultInitValue]
        /\ remote_peer = [self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..MAX_PEERS -> "Listening"
                                        [] self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) -> "Connect"
                                        [] self = 0 -> "AddPeer"]

VersionMessage(self) == /\ pc[self] = "VersionMessage"
                        /\ message_header' = [message_header EXCEPT ![self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] =                                                          [
                                                                                                                   start_string |-> "f9beb4d9",
                                                                                                                   command_name |-> "version",
                                                                                                                   payload_size |-> 1,
                                                                                                                   checksum |-> "0x5df6e0e2"]]
                        /\ message_payload' = [message_payload EXCEPT ![self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] =                                                           [
                                                                                                                     version |-> "70015",
                                                                                                                     services |-> "0x01",
                                                                                                                     timestamp |-> "",
                                                                                                                     addr_recv |-> local_peer_addr_c[self],
                                                                                                                     addr_trans |-> remote_peer_addr[self],
                                                                                                                     nonce |-> "",
                                                                                                                     user_agent |-> "",
                                                                                                                     start_height |-> GetPeerFromNetwork(ToSet(the_network), remote_peer_addr[self]).chain_tip,
                                                                                                                     relay |-> ""]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = Head(stack[self]).remote_peer_addr]
                        /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT ![self] = Head(stack[self]).local_peer_addr_c]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        local_peer_addr_g, hashes, 
                                        found_blocks, blocks, hashes_, 
                                        block_headers, local_peer_addr, 
                                        inventory, c, block_data, 
                                        remote_peer_addr_, local_peer_addr_, 
                                        remote_peer_addr_P, remote_peer >>

create_connection(self) == VersionMessage(self)

VerackMessage(self) == /\ pc[self] = "VerackMessage"
                       /\ message_header' = [message_header EXCEPT ![self] =                     [
                                                                             start_string |-> "f9beb4d9",
                                                                             command_name |-> "verack",
                                                                             payload_size |-> 0,
                                                                             checksum |-> "0x5df6e0e2"]]
                       /\ message_payload' = [message_payload EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << the_network, selected_remote_peer, 
                                       remote_peer_addr, local_peer_addr_c, 
                                       local_peer_addr_g, hashes, found_blocks, 
                                       blocks, hashes_, block_headers, 
                                       local_peer_addr, inventory, c, 
                                       block_data, remote_peer_addr_, 
                                       local_peer_addr_, remote_peer_addr_P, 
                                       remote_peer >>

send_verack(self) == VerackMessage(self)

GetPeerFromTheNetwork(self) == /\ pc[self] = "GetPeerFromTheNetwork"
                               /\ Len(the_network) >= 2
                               /\ selected_remote_peer' =                         GetPeerFromNetwork(
                                                              ToSet(the_network),
                                                              CHOOSE peer_set \in GetPeerFromNetwork(ToSet(the_network), local_peer_addr_g[self]).peer_set : TRUE
                                                          )
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ local_peer_addr_g' = [local_peer_addr_g EXCEPT ![self] = Head(stack[self]).local_peer_addr_g]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << the_network, message_header, 
                                               message_payload, 
                                               remote_peer_addr, 
                                               local_peer_addr_c, hashes, 
                                               found_blocks, blocks, hashes_, 
                                               block_headers, local_peer_addr, 
                                               inventory, c, block_data, 
                                               remote_peer_addr_, 
                                               local_peer_addr_, 
                                               remote_peer_addr_P, remote_peer >>

get_peer_from_the_network(self) == GetPeerFromTheNetwork(self)

GetBlocksMessage(self) == /\ pc[self] = "GetBlocksMessage"
                          /\ message_header' = [message_header EXCEPT ![self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] =                                                          [
                                                                                                                     start_string |-> "f9beb4d9",
                                                                                                                     command_name |-> "getblocks",
                                                                                                                     payload_size |-> 1,
                                                                                                                     checksum |-> "0x5df6e0e2"]]
                          /\ message_payload' = [message_payload EXCEPT ![self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] =                                                           [
                                                                                                                       version |-> "70015",
                                                                                                                       
                                                                                                                       hash_count |-> Len(hashes[self]),
                                                                                                                       block_header_hashes |-> hashes[self],
                                                                                                                       stop_hash |-> "0"]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ hashes' = [hashes EXCEPT ![self] = Head(stack[self]).hashes]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          remote_peer_addr, local_peer_addr_c, 
                                          local_peer_addr_g, found_blocks, 
                                          blocks, hashes_, block_headers, 
                                          local_peer_addr, inventory, c, 
                                          block_data, remote_peer_addr_, 
                                          local_peer_addr_, remote_peer_addr_P, 
                                          remote_peer >>

request_blocks(self) == GetBlocksMessage(self)

ProcessForInventory(self) == /\ pc[self] = "ProcessForInventory"
                             /\ blocks' = [blocks EXCEPT ![self] = { r \in DOMAIN found_blocks[self] : found_blocks[self][r] = TRUE }]
                             /\ hashes_' = [hashes_ EXCEPT ![self] = SetToSeq({ s.hash : s \in blocks'[self] })]
                             /\ block_headers' = [block_headers EXCEPT ![self] =                  [
                                                                                     h \in 1..Len(hashes_'[self]) |-> [
                                                                                         type_identifier |-> "MSG_BLOCK",
                                                                                         hash |-> hashes_'[self][h]
                                                                                     ]
                                                                                 ]]
                             /\ pc' = [pc EXCEPT ![self] = "InventoryMessage"]
                             /\ UNCHANGED << the_network, selected_remote_peer, 
                                             message_header, message_payload, 
                                             stack, remote_peer_addr, 
                                             local_peer_addr_c, 
                                             local_peer_addr_g, hashes, 
                                             found_blocks, local_peer_addr, 
                                             inventory, c, block_data, 
                                             remote_peer_addr_, 
                                             local_peer_addr_, 
                                             remote_peer_addr_P, remote_peer >>

InventoryMessage(self) == /\ pc[self] = "InventoryMessage"
                          /\ message_header' = [message_header EXCEPT ![self] =                     [
                                                                                start_string |-> "f9beb4d9",
                                                                                command_name |-> "inv",
                                                                                payload_size |-> 1,
                                                                                checksum |-> "0x5df6e0e2"]]
                          /\ message_payload' = [message_payload EXCEPT ![self] =                          [
                                                                                      count |-> Len(block_headers[self]),
                                                                                      inventory |-> block_headers[self]
                                                                                  ]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ blocks' = [blocks EXCEPT ![self] = Head(stack[self]).blocks]
                          /\ hashes_' = [hashes_ EXCEPT ![self] = Head(stack[self]).hashes_]
                          /\ block_headers' = [block_headers EXCEPT ![self] = Head(stack[self]).block_headers]
                          /\ found_blocks' = [found_blocks EXCEPT ![self] = Head(stack[self]).found_blocks]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          remote_peer_addr, local_peer_addr_c, 
                                          local_peer_addr_g, hashes, 
                                          local_peer_addr, inventory, c, 
                                          block_data, remote_peer_addr_, 
                                          local_peer_addr_, remote_peer_addr_P, 
                                          remote_peer >>

build_inventory_message(self) == ProcessForInventory(self)
                                    \/ InventoryMessage(self)

GetDataMessage(self) == /\ pc[self] = "GetDataMessage"
                        /\ message_header' = [message_header EXCEPT ![self] =                     [
                                                                              start_string |-> "f9beb4d9",
                                                                              command_name |-> "getdata",
                                                                              payload_size |-> message_payload[self].count,
                                                                              checksum |-> "0x5df6e0e2"]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        message_payload, remote_peer_addr, 
                                        local_peer_addr_c, local_peer_addr_g, 
                                        hashes, found_blocks, blocks, hashes_, 
                                        block_headers, local_peer_addr, 
                                        inventory, c, block_data, 
                                        remote_peer_addr_, local_peer_addr_, 
                                        remote_peer_addr_P, remote_peer >>

process_inventory_message(self) == GetDataMessage(self)

IncorporateLoop(self) == /\ pc[self] = "IncorporateLoop"
                         /\ IF c[self] <= Len(message_payload[self].inventory)
                               THEN /\ block_data' = [block_data EXCEPT ![self] = FindBlockByHash(selected_remote_peer.blocks, message_payload[self].inventory[c[self]].hash)]
                                    /\ Assert(block_data'[self].hash = message_payload[self].inventory[c[self]].hash, 
                                              "Failure of assertion at line 197, column 13.")
                                    /\ the_network' =                UpdatePeerBlocks(local_peer_addr[self], [
                                                          height |-> block_data'[self].height,
                                                          hash |-> block_data'[self].hash,
                                                          block |-> block_data'[self].block
                                                      ])
                                    /\ c' = [c EXCEPT ![self] = c[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateTip"]
                                    /\ UNCHANGED << the_network, c, block_data >>
                         /\ UNCHANGED << selected_remote_peer, message_header, 
                                         message_payload, stack, 
                                         remote_peer_addr, local_peer_addr_c, 
                                         local_peer_addr_g, hashes, 
                                         found_blocks, blocks, hashes_, 
                                         block_headers, local_peer_addr, 
                                         inventory, remote_peer_addr_, 
                                         local_peer_addr_, remote_peer_addr_P, 
                                         remote_peer >>

UpdateTip(self) == /\ pc[self] = "UpdateTip"
                   /\ the_network' = UpdatePeerTip(local_peer_addr[self], block_data[self].height)
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                   /\ block_data' = [block_data EXCEPT ![self] = Head(stack[self]).block_data]
                   /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = Head(stack[self]).local_peer_addr]
                   /\ inventory' = [inventory EXCEPT ![self] = Head(stack[self]).inventory]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << selected_remote_peer, message_header, 
                                   message_payload, remote_peer_addr, 
                                   local_peer_addr_c, local_peer_addr_g, 
                                   hashes, found_blocks, blocks, hashes_, 
                                   block_headers, remote_peer_addr_, 
                                   local_peer_addr_, remote_peer_addr_P, 
                                   remote_peer >>

incorporate_data_to_local_peer(self) == IncorporateLoop(self)
                                           \/ UpdateTip(self)

Listening(self) == /\ pc[self] = "Listening"
                   /\ self > 1
                   /\ Len(the_network) >= self
                   /\ Len(message_header) >= self
                   /\ IF message_header[self] = defaultInitValue
                         THEN /\ pc' = [pc EXCEPT ![self] = "Listening"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Requests"]
                   /\ UNCHANGED << the_network, selected_remote_peer, 
                                   message_header, message_payload, stack, 
                                   remote_peer_addr, local_peer_addr_c, 
                                   local_peer_addr_g, hashes, found_blocks, 
                                   blocks, hashes_, block_headers, 
                                   local_peer_addr, inventory, c, block_data, 
                                   remote_peer_addr_, local_peer_addr_, 
                                   remote_peer_addr_P, remote_peer >>

Requests(self) == /\ pc[self] = "Requests"
                  /\ IF message_header[self].command_name = "version"
                        THEN /\ local_peer_addr_' = [local_peer_addr_ EXCEPT ![self] = message_payload[self].addr_recv]
                             /\ remote_peer_addr_' = [remote_peer_addr_ EXCEPT ![self] = message_payload[self].addr_trans]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_verack",
                                                                      pc        |->  "Requests" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "VerackMessage"]
                             /\ UNCHANGED << the_network, found_blocks, blocks, 
                                             hashes_, block_headers, 
                                             local_peer_addr, inventory, c, 
                                             block_data >>
                        ELSE /\ IF message_header[self].command_name = "verack"
                                   THEN /\ the_network' = UpdatePeerSet(local_peer_addr_[self], remote_peer_addr_[self])
                                        /\ pc' = [pc EXCEPT ![self] = "ClientTaskLoop"]
                                        /\ UNCHANGED << stack, found_blocks, 
                                                        blocks, hashes_, 
                                                        block_headers, 
                                                        local_peer_addr, 
                                                        inventory, c, 
                                                        block_data >>
                                   ELSE /\ IF message_header[self].command_name = "getblocks"
                                              THEN /\ IF message_payload[self].hash_count = 0
                                                         THEN /\ /\ found_blocks' = [found_blocks EXCEPT ![self] = FindBlocks(selected_remote_peer.blocks, 1, 1 + (MaxGetBlocksInvResponse - 1))]
                                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "build_inventory_message",
                                                                                                          pc        |->  "Requests",
                                                                                                          blocks    |->  blocks[self],
                                                                                                          hashes_   |->  hashes_[self],
                                                                                                          block_headers |->  block_headers[self],
                                                                                                          found_blocks |->  found_blocks[self] ] >>
                                                                                                      \o stack[self]]
                                                              /\ blocks' = [blocks EXCEPT ![self] = defaultInitValue]
                                                              /\ hashes_' = [hashes_ EXCEPT ![self] = defaultInitValue]
                                                              /\ block_headers' = [block_headers EXCEPT ![self] = defaultInitValue]
                                                              /\ pc' = [pc EXCEPT ![self] = "ProcessForInventory"]
                                                         ELSE /\ /\ found_blocks' = [found_blocks EXCEPT ![self] = FindBlocks(selected_remote_peer.blocks, 4, 4 + (MaxGetBlocksInvResponse - 1))]
                                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "build_inventory_message",
                                                                                                          pc        |->  "Requests",
                                                                                                          blocks    |->  blocks[self],
                                                                                                          hashes_   |->  hashes_[self],
                                                                                                          block_headers |->  block_headers[self],
                                                                                                          found_blocks |->  found_blocks[self] ] >>
                                                                                                      \o stack[self]]
                                                              /\ blocks' = [blocks EXCEPT ![self] = defaultInitValue]
                                                              /\ hashes_' = [hashes_ EXCEPT ![self] = defaultInitValue]
                                                              /\ block_headers' = [block_headers EXCEPT ![self] = defaultInitValue]
                                                              /\ pc' = [pc EXCEPT ![self] = "ProcessForInventory"]
                                                   /\ UNCHANGED << local_peer_addr, 
                                                                   inventory, 
                                                                   c, 
                                                                   block_data >>
                                              ELSE /\ IF message_header[self].command_name = "inv"
                                                         THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "process_inventory_message",
                                                                                                       pc        |->  "Requests" ] >>
                                                                                                   \o stack[self]]
                                                              /\ pc' = [pc EXCEPT ![self] = "GetDataMessage"]
                                                              /\ UNCHANGED << local_peer_addr, 
                                                                              inventory, 
                                                                              c, 
                                                                              block_data >>
                                                         ELSE /\ IF message_header[self].command_name = "getdata"
                                                                    THEN /\ /\ inventory' = [inventory EXCEPT ![self] = message_payload[self].inventory]
                                                                            /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = local_peer_addr_[self]]
                                                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "incorporate_data_to_local_peer",
                                                                                                                     pc        |->  "ClientTaskLoop",
                                                                                                                     c         |->  c[self],
                                                                                                                     block_data |->  block_data[self],
                                                                                                                     local_peer_addr |->  local_peer_addr[self],
                                                                                                                     inventory |->  inventory[self] ] >>
                                                                                                                 \o stack[self]]
                                                                         /\ c' = [c EXCEPT ![self] = 1]
                                                                         /\ block_data' = [block_data EXCEPT ![self] = defaultInitValue]
                                                                         /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "ClientTaskLoop"]
                                                                         /\ UNCHANGED << stack, 
                                                                                         local_peer_addr, 
                                                                                         inventory, 
                                                                                         c, 
                                                                                         block_data >>
                                                   /\ UNCHANGED << found_blocks, 
                                                                   blocks, 
                                                                   hashes_, 
                                                                   block_headers >>
                                        /\ UNCHANGED the_network
                             /\ UNCHANGED << remote_peer_addr_, 
                                             local_peer_addr_ >>
                  /\ UNCHANGED << selected_remote_peer, message_header, 
                                  message_payload, remote_peer_addr, 
                                  local_peer_addr_c, local_peer_addr_g, hashes, 
                                  remote_peer_addr_P, remote_peer >>

ClientTaskLoop(self) == /\ pc[self] = "ClientTaskLoop"
                        /\ message_header' = [message_header EXCEPT ![self] = defaultInitValue]
                        /\ message_payload' = [message_payload EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "Listening"]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        stack, remote_peer_addr, 
                                        local_peer_addr_c, local_peer_addr_g, 
                                        hashes, found_blocks, blocks, hashes_, 
                                        block_headers, local_peer_addr, 
                                        inventory, c, block_data, 
                                        remote_peer_addr_, local_peer_addr_, 
                                        remote_peer_addr_P, remote_peer >>

client_task(self) == Listening(self) \/ Requests(self)
                        \/ ClientTaskLoop(self)

Connect(self) == /\ pc[self] = "Connect"
                 /\ Len(the_network) = MAX_PEERS
                 /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].peer]
                 /\ remote_peer_addr_P' = [remote_peer_addr_P EXCEPT ![self] = "peer1"]
                 /\ self > (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)
                 /\ /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT ![self] = local_peer_addr'[self]]
                    /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = remote_peer_addr_P'[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "create_connection",
                                                             pc        |->  "SelectPeerForRequestFromLocalPeer",
                                                             remote_peer_addr |->  remote_peer_addr[self],
                                                             local_peer_addr_c |->  local_peer_addr_c[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "VersionMessage"]
                 /\ UNCHANGED << the_network, selected_remote_peer, 
                                 message_header, message_payload, 
                                 local_peer_addr_g, hashes, found_blocks, 
                                 blocks, hashes_, block_headers, inventory, c, 
                                 block_data, remote_peer_addr_, 
                                 local_peer_addr_, remote_peer >>

SelectPeerForRequestFromLocalPeer(self) == /\ pc[self] = "SelectPeerForRequestFromLocalPeer"
                                           /\ Len(the_network) = MAX_PEERS /\ Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].peer_set) > 0
                                           /\ /\ local_peer_addr_g' = [local_peer_addr_g EXCEPT ![self] = local_peer_addr[self]]
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_peer_from_the_network",
                                                                                       pc        |->  "RequestInventory",
                                                                                       local_peer_addr_g |->  local_peer_addr_g[self] ] >>
                                                                                   \o stack[self]]
                                           /\ pc' = [pc EXCEPT ![self] = "GetPeerFromTheNetwork"]
                                           /\ UNCHANGED << the_network, 
                                                           selected_remote_peer, 
                                                           message_header, 
                                                           message_payload, 
                                                           remote_peer_addr, 
                                                           local_peer_addr_c, 
                                                           hashes, 
                                                           found_blocks, 
                                                           blocks, hashes_, 
                                                           block_headers, 
                                                           local_peer_addr, 
                                                           inventory, c, 
                                                           block_data, 
                                                           remote_peer_addr_, 
                                                           local_peer_addr_, 
                                                           remote_peer_addr_P, 
                                                           remote_peer >>

RequestInventory(self) == /\ pc[self] = "RequestInventory"
                          /\ Cardinality(the_network[1].blocks) > 0
                          /\ Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].blocks) = 0
                          /\ /\ hashes' = [hashes EXCEPT ![self] = <<>>]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                      pc        |->  "RequestMoreBlocks",
                                                                      hashes    |->  hashes[self] ] >>
                                                                  \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "GetBlocksMessage"]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          message_header, message_payload, 
                                          remote_peer_addr, local_peer_addr_c, 
                                          local_peer_addr_g, found_blocks, 
                                          blocks, hashes_, block_headers, 
                                          local_peer_addr, inventory, c, 
                                          block_data, remote_peer_addr_, 
                                          local_peer_addr_, remote_peer_addr_P, 
                                          remote_peer >>

RequestMoreBlocks(self) == /\ pc[self] = "RequestMoreBlocks"
                           /\ Cardinality(the_network[1].blocks) = 4
                           /\ Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].blocks) = 3
                           /\ message_header[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] = defaultInitValue
                           /\ message_payload[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES] = defaultInitValue
                           /\ /\ hashes' = [hashes EXCEPT ![self] = <<"blockhash4">>]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                       pc        |->  "CheckSync",
                                                                       hashes    |->  hashes[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "GetBlocksMessage"]
                           /\ UNCHANGED << the_network, selected_remote_peer, 
                                           message_header, message_payload, 
                                           remote_peer_addr, local_peer_addr_c, 
                                           local_peer_addr_g, found_blocks, 
                                           blocks, hashes_, block_headers, 
                                           local_peer_addr, inventory, c, 
                                           block_data, remote_peer_addr_, 
                                           local_peer_addr_, 
                                           remote_peer_addr_P, remote_peer >>

CheckSync(self) == /\ pc[self] = "CheckSync"
                   /\ Cardinality(the_network[1].blocks) = 4
                   /\ Cardinality(the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].blocks) = 4
                   /\ the_network[self - IDENTIFIER_DIFFERENCE_OF_PROCESSES].chain_tip = 4
                   /\ PrintT("Network in sync!")
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << the_network, selected_remote_peer, 
                                   message_header, message_payload, stack, 
                                   remote_peer_addr, local_peer_addr_c, 
                                   local_peer_addr_g, hashes, found_blocks, 
                                   blocks, hashes_, block_headers, 
                                   local_peer_addr, inventory, c, block_data, 
                                   remote_peer_addr_, local_peer_addr_, 
                                   remote_peer_addr_P, remote_peer >>

Peer(self) == Connect(self) \/ SelectPeerForRequestFromLocalPeer(self)
                 \/ RequestInventory(self) \/ RequestMoreBlocks(self)
                 \/ CheckSync(self)

AddPeer == /\ pc[0] = "AddPeer"
           /\ the_network' = <<PEER1, PEER2>>
           /\ pc' = [pc EXCEPT ![0] = "Done"]
           /\ UNCHANGED << selected_remote_peer, message_header, 
                           message_payload, stack, remote_peer_addr, 
                           local_peer_addr_c, local_peer_addr_g, hashes, 
                           found_blocks, blocks, hashes_, block_headers, 
                           local_peer_addr, inventory, c, block_data, 
                           remote_peer_addr_, local_peer_addr_, 
                           remote_peer_addr_P, remote_peer >>

Main == AddPeer

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Main
           \/ (\E self \in ProcSet:  \/ create_connection(self)
                                     \/ send_verack(self)
                                     \/ get_peer_from_the_network(self)
                                     \/ request_blocks(self)
                                     \/ build_inventory_message(self)
                                     \/ process_inventory_message(self)
                                     \/ incorporate_data_to_local_peer(self))
           \/ (\E self \in 1..MAX_PEERS: client_task(self))
           \/ (\E self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS): Peer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
