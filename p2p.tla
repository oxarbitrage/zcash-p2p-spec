---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils

MaxGetBlocksInvResponse == 3

(*--algorithm p2p

variables
    the_network = <<>>;
    selected_remote_peer;
    message_header;
    message_payload;
define
    \* Given a block collection and a hash, returns the block with the given hash.
    FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash
    
    \* Updates the blocks of a peer in the network.
    UpdatePeerBlocks(peer_address, newBlocks) == [i \in 1..Len(the_network) |-> 
        IF the_network[i].peer = peer_address THEN
            [the_network[i] EXCEPT !.blocks = @ \cup {newBlocks}] 
        ELSE
            the_network[i]
    ]

    \* Given a block collection, a start height and an end height, returns the blocks in the given range.
    FindBlocks(block_collection, start_height, end_height) == 
        [b \in block_collection |-> b.height >= start_height /\ b.height <= end_height]
    
    \* Get the peer set of a peer given a peer address and the network state as a set.
    GetPeerFromNetwork(state, peer_address) == CHOOSE rec \in state : rec.peer = peer_address
end define;

\* Define initial network conditions, we should have at least 1 peer with some blocks in the network.
procedure initial_conditions() 
begin
    AddPeer1:
        the_network := Append(the_network, [peer |-> "peer1", blocks |-> {
            [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
            [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
            [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
            [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"]
        }, peer_set |-> {}]);
    return;
end procedure;

\* Create a connection between the remote and local peer.
procedure create_connection(remote_peer_addr, local_peer_addr)
begin
    VersionMessage:
        \* TODO: check if addr_recv exist in the network.
        \* TODO: check if addr_trans do not exist in the network?

        \* Create a message header.
        message_header := [
            start_string |-> "f9beb4d9",
            command_name |-> "version",
            payload_size |-> 1,
            checksum |-> "0x5df6e0e2"];
    
        \* Create a version message from local_peer_addr requesting connection with remote_peer_addr
        message_payload := [
            version |-> "70015",
            services |-> "0x01",
            timestamp |-> "",
            addr_recv |-> local_peer_addr,
            addr_trans |-> remote_peer_addr,
            nonce |-> "",
            user_agent |-> "",
            start_height |-> 0,
            relay |-> ""];
    return;
end procedure;

\* Send a verack message to the remote peer.
procedure send_verack()
begin
    VerackMessage:
        message_header := [
            start_string |-> "f9beb4d9",
            command_name |-> "verack", 
            payload_size |-> 0,
            checksum |-> "0x5df6e0e2"];
        message_payload := defaultInitValue;
    return;
end procedure;

\* Append a peer to the network with a remote peer added in the peer_set. 
\* Assumes connection was established before.
procedure append_peer_to_the_network(local_peer_addr, remote_peer_addr)
begin
    AppendPeerToTheNetwork:
        the_network := Append(the_network, [
            peer |-> local_peer_addr,
            blocks |-> {}, \* empty blocks for now
            peer_set |-> {remote_peer_addr}
        ]);
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
        message_header := [
            start_string |-> "f9beb4d9",
            command_name |-> "getblocks", 
            payload_size |-> 1,
            checksum |-> "0x5df6e0e2"];
        
        message_payload := [
            version |-> "70015",
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
        block_headers := [h \in 1..Len(hashes) |-> [type_identifier |-> "MSG_BLOCK", hash |-> hashes[h]]];
    InventoryMessage:
        message_header := [
            start_string |-> "f9beb4d9",
            command_name |-> "inv", 
            payload_size |-> 1,
            checksum |-> "0x5df6e0e2"];

        message_payload := [count |-> Len(block_headers), inventory |-> block_headers];
    return;
end procedure;

\* Build getdata messages with the inventory received.
procedure process_inventory_message(payload)
begin
    GetDataMessage:
        \* Validate the inventory? For now we just pass it as it came so we just change the global message header.
        message_header := [
            start_string |-> "f9beb4d9",
            command_name |-> "getdata", 
            payload_size |-> payload.count,
            checksum |-> "0x5df6e0e2"];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure incorporate_data_to_local_peer(local_peer_addr, inventory)
variables c = 1, block_data;
begin
    \* Here we are sure the selected peer has the requested blocks.
    IncorporateLoop:
        while c <= Len(message_payload.inventory) do
            block_data := FindBlockByHash(selected_remote_peer.blocks, message_payload.inventory[c].hash);
            assert block_data.hash = message_payload.inventory[c].hash;
                            
            the_network := UpdatePeerBlocks(local_peer_addr, [
                height |-> block_data.height,
                hash |-> block_data.hash,
                block |-> block_data.block
            ]);        
            c := c + 1;
        end while;
    return;
end procedure;

\* Peer Client Task
process client_task = "Peer Client Task"
variables remote_peer_addr, local_peer_addr;
begin
    WaitForCommand:
        if message_header # defaultInitValue then
            goto Requests;
        else 
            goto WaitForCommand;
        end if;
    Requests:
        if message_header.command_name = "version" then
            local_peer_addr := message_payload.addr_recv;
            remote_peer_addr := message_payload.addr_trans;
            call send_verack();
            goto Requests;
        elsif message_header.command_name = "verack" then
            call append_peer_to_the_network(local_peer_addr, remote_peer_addr);
        elsif message_header.command_name = "getblocks" then
            call build_inventory_message(FindBlocks(selected_remote_peer.blocks, 1, MaxGetBlocksInvResponse));
            goto Requests;    
        elsif message_header.command_name = "inv" then
            call process_inventory_message(message_payload);
            goto Requests;
        elsif message_header.command_name = "getdata" then
            call incorporate_data_to_local_peer(local_peer_addr, message_payload.inventory);
        end if;
    ClientTaskLoop:
        message_header := defaultInitValue;
        message_payload := defaultInitValue;
        goto WaitForCommand;
end process;

process Main = "Main"
variables local_peer_addr, remote_peer_addr;
begin
    Setup:
        call initial_conditions();
    CreateConnection:
        local_peer_addr := "peer8";
        remote_peer_addr := "peer1";
        call create_connection(remote_peer_addr, local_peer_addr);
    SelectPeerForRequestFromLocalPeer:
        await Len(the_network) = 2;
        call get_peer_from_the_network(local_peer_addr);
    RequestInventory:
        call request_blocks(<<>>);
    CheckStatus:
        \* Not in sync yet.
        await Cardinality(the_network[1].blocks) = 4;
        await Cardinality(the_network[2].blocks) = 3;
    RequestMoreBlocks:
        \*print(GetPeerFromNetwork(ToSet(the_network), local_peer));
        skip;
        \*call request_blocks(<<"blockhash3">>);
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "71a8c678" /\ chksum(tla) = "fbe0858a")
\* Process variable remote_peer_addr of process client_task at line 186 col 11 changed to remote_peer_addr_
\* Process variable local_peer_addr of process client_task at line 186 col 29 changed to local_peer_addr_
\* Process variable local_peer_addr of process Main at line 218 col 11 changed to local_peer_addr_M
\* Process variable remote_peer_addr of process Main at line 218 col 28 changed to remote_peer_addr_M
\* Procedure variable hashes of procedure build_inventory_message at line 134 col 19 changed to hashes_
\* Parameter remote_peer_addr of procedure create_connection at line 47 col 29 changed to remote_peer_addr_c
\* Parameter local_peer_addr of procedure create_connection at line 47 col 47 changed to local_peer_addr_c
\* Parameter local_peer_addr of procedure append_peer_to_the_network at line 89 col 38 changed to local_peer_addr_a
\* Parameter local_peer_addr of procedure get_peer_from_the_network at line 101 col 37 changed to local_peer_addr_g
CONSTANT defaultInitValue
VARIABLES the_network, selected_remote_peer, message_header, message_payload, 
          pc, stack

(* define statement *)
FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash


UpdatePeerBlocks(peer_address, newBlocks) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = peer_address THEN
        [the_network[i] EXCEPT !.blocks = @ \cup {newBlocks}]
    ELSE
        the_network[i]
]


FindBlocks(block_collection, start_height, end_height) ==
    [b \in block_collection |-> b.height >= start_height /\ b.height <= end_height]


GetPeerFromNetwork(state, peer_address) == CHOOSE rec \in state : rec.peer = peer_address

VARIABLES remote_peer_addr_c, local_peer_addr_c, local_peer_addr_a, 
          remote_peer_addr, local_peer_addr_g, hashes, found_blocks, blocks, 
          hashes_, block_headers, payload, local_peer_addr, inventory, c, 
          block_data, remote_peer_addr_, local_peer_addr_, local_peer_addr_M, 
          remote_peer_addr_M

vars == << the_network, selected_remote_peer, message_header, message_payload, 
           pc, stack, remote_peer_addr_c, local_peer_addr_c, 
           local_peer_addr_a, remote_peer_addr, local_peer_addr_g, hashes, 
           found_blocks, blocks, hashes_, block_headers, payload, 
           local_peer_addr, inventory, c, block_data, remote_peer_addr_, 
           local_peer_addr_, local_peer_addr_M, remote_peer_addr_M >>

ProcSet == {"Peer Client Task"} \cup {"Main"}

Init == (* Global variables *)
        /\ the_network = <<>>
        /\ selected_remote_peer = defaultInitValue
        /\ message_header = defaultInitValue
        /\ message_payload = defaultInitValue
        (* Procedure create_connection *)
        /\ remote_peer_addr_c = [ self \in ProcSet |-> defaultInitValue]
        /\ local_peer_addr_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure append_peer_to_the_network *)
        /\ local_peer_addr_a = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_peer_from_the_network *)
        /\ local_peer_addr_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure build_inventory_message *)
        /\ found_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ hashes_ = [ self \in ProcSet |-> defaultInitValue]
        /\ block_headers = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure process_inventory_message *)
        /\ payload = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure incorporate_data_to_local_peer *)
        /\ local_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ inventory = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> 1]
        /\ block_data = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_task *)
        /\ remote_peer_addr_ = defaultInitValue
        /\ local_peer_addr_ = defaultInitValue
        (* Process Main *)
        /\ local_peer_addr_M = defaultInitValue
        /\ remote_peer_addr_M = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "Peer Client Task" -> "WaitForCommand"
                                        [] self = "Main" -> "Setup"]

AddPeer1(self) == /\ pc[self] = "AddPeer1"
                  /\ the_network' =                Append(the_network, [peer |-> "peer1", blocks |-> {
                                        [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
                                        [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
                                        [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
                                        [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"]
                                    }, peer_set |-> {}])
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << selected_remote_peer, message_header, 
                                  message_payload, remote_peer_addr_c, 
                                  local_peer_addr_c, local_peer_addr_a, 
                                  remote_peer_addr, local_peer_addr_g, hashes, 
                                  found_blocks, blocks, hashes_, block_headers, 
                                  payload, local_peer_addr, inventory, c, 
                                  block_data, remote_peer_addr_, 
                                  local_peer_addr_, local_peer_addr_M, 
                                  remote_peer_addr_M >>

initial_conditions(self) == AddPeer1(self)

VersionMessage(self) == /\ pc[self] = "VersionMessage"
                        /\ message_header' =               [
                                             start_string |-> "f9beb4d9",
                                             command_name |-> "version",
                                             payload_size |-> 1,
                                             checksum |-> "0x5df6e0e2"]
                        /\ message_payload' =                [
                                              version |-> "70015",
                                              services |-> "0x01",
                                              timestamp |-> "",
                                              addr_recv |-> local_peer_addr_c[self],
                                              addr_trans |-> remote_peer_addr_c[self],
                                              nonce |-> "",
                                              user_agent |-> "",
                                              start_height |-> 0,
                                              relay |-> ""]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ remote_peer_addr_c' = [remote_peer_addr_c EXCEPT ![self] = Head(stack[self]).remote_peer_addr_c]
                        /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT ![self] = Head(stack[self]).local_peer_addr_c]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        local_peer_addr_a, remote_peer_addr, 
                                        local_peer_addr_g, hashes, 
                                        found_blocks, blocks, hashes_, 
                                        block_headers, payload, 
                                        local_peer_addr, inventory, c, 
                                        block_data, remote_peer_addr_, 
                                        local_peer_addr_, local_peer_addr_M, 
                                        remote_peer_addr_M >>

create_connection(self) == VersionMessage(self)

VerackMessage(self) == /\ pc[self] = "VerackMessage"
                       /\ message_header' =               [
                                            start_string |-> "f9beb4d9",
                                            command_name |-> "verack",
                                            payload_size |-> 0,
                                            checksum |-> "0x5df6e0e2"]
                       /\ message_payload' = defaultInitValue
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << the_network, selected_remote_peer, 
                                       remote_peer_addr_c, local_peer_addr_c, 
                                       local_peer_addr_a, remote_peer_addr, 
                                       local_peer_addr_g, hashes, found_blocks, 
                                       blocks, hashes_, block_headers, payload, 
                                       local_peer_addr, inventory, c, 
                                       block_data, remote_peer_addr_, 
                                       local_peer_addr_, local_peer_addr_M, 
                                       remote_peer_addr_M >>

send_verack(self) == VerackMessage(self)

AppendPeerToTheNetwork(self) == /\ pc[self] = "AppendPeerToTheNetwork"
                                /\ the_network' =                Append(the_network, [
                                                      peer |-> local_peer_addr_a[self],
                                                      blocks |-> {},
                                                      peer_set |-> {remote_peer_addr[self]}
                                                  ])
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ local_peer_addr_a' = [local_peer_addr_a EXCEPT ![self] = Head(stack[self]).local_peer_addr_a]
                                /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = Head(stack[self]).remote_peer_addr]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << selected_remote_peer, 
                                                message_header, 
                                                message_payload, 
                                                remote_peer_addr_c, 
                                                local_peer_addr_c, 
                                                local_peer_addr_g, hashes, 
                                                found_blocks, blocks, hashes_, 
                                                block_headers, payload, 
                                                local_peer_addr, inventory, c, 
                                                block_data, remote_peer_addr_, 
                                                local_peer_addr_, 
                                                local_peer_addr_M, 
                                                remote_peer_addr_M >>

append_peer_to_the_network(self) == AppendPeerToTheNetwork(self)

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
                                               remote_peer_addr_c, 
                                               local_peer_addr_c, 
                                               local_peer_addr_a, 
                                               remote_peer_addr, hashes, 
                                               found_blocks, blocks, hashes_, 
                                               block_headers, payload, 
                                               local_peer_addr, inventory, c, 
                                               block_data, remote_peer_addr_, 
                                               local_peer_addr_, 
                                               local_peer_addr_M, 
                                               remote_peer_addr_M >>

get_peer_from_the_network(self) == GetPeerFromTheNetwork(self)

GetBlocksMessage(self) == /\ pc[self] = "GetBlocksMessage"
                          /\ message_header' =               [
                                               start_string |-> "f9beb4d9",
                                               command_name |-> "getblocks",
                                               payload_size |-> 1,
                                               checksum |-> "0x5df6e0e2"]
                          /\ message_payload' =                [
                                                version |-> "70015",
                                                hash_count |-> Len(hashes[self]),
                                                block_header_hashes |-> hashes[self],
                                                stop_hash |-> "0"]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ hashes' = [hashes EXCEPT ![self] = Head(stack[self]).hashes]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          remote_peer_addr_c, 
                                          local_peer_addr_c, local_peer_addr_a, 
                                          remote_peer_addr, local_peer_addr_g, 
                                          found_blocks, blocks, hashes_, 
                                          block_headers, payload, 
                                          local_peer_addr, inventory, c, 
                                          block_data, remote_peer_addr_, 
                                          local_peer_addr_, local_peer_addr_M, 
                                          remote_peer_addr_M >>

request_blocks(self) == GetBlocksMessage(self)

ProcessForInventory(self) == /\ pc[self] = "ProcessForInventory"
                             /\ blocks' = [blocks EXCEPT ![self] = { r \in DOMAIN found_blocks[self] : found_blocks[self][r] = TRUE }]
                             /\ hashes_' = [hashes_ EXCEPT ![self] = SetToSeq({ s.hash : s \in blocks'[self] })]
                             /\ block_headers' = [block_headers EXCEPT ![self] = [h \in 1..Len(hashes_'[self]) |-> [type_identifier |-> "MSG_BLOCK", hash |-> hashes_'[self][h]]]]
                             /\ pc' = [pc EXCEPT ![self] = "InventoryMessage"]
                             /\ UNCHANGED << the_network, selected_remote_peer, 
                                             message_header, message_payload, 
                                             stack, remote_peer_addr_c, 
                                             local_peer_addr_c, 
                                             local_peer_addr_a, 
                                             remote_peer_addr, 
                                             local_peer_addr_g, hashes, 
                                             found_blocks, payload, 
                                             local_peer_addr, inventory, c, 
                                             block_data, remote_peer_addr_, 
                                             local_peer_addr_, 
                                             local_peer_addr_M, 
                                             remote_peer_addr_M >>

InventoryMessage(self) == /\ pc[self] = "InventoryMessage"
                          /\ message_header' =               [
                                               start_string |-> "f9beb4d9",
                                               command_name |-> "inv",
                                               payload_size |-> 1,
                                               checksum |-> "0x5df6e0e2"]
                          /\ message_payload' = [count |-> Len(block_headers[self]), inventory |-> block_headers[self]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ blocks' = [blocks EXCEPT ![self] = Head(stack[self]).blocks]
                          /\ hashes_' = [hashes_ EXCEPT ![self] = Head(stack[self]).hashes_]
                          /\ block_headers' = [block_headers EXCEPT ![self] = Head(stack[self]).block_headers]
                          /\ found_blocks' = [found_blocks EXCEPT ![self] = Head(stack[self]).found_blocks]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          remote_peer_addr_c, 
                                          local_peer_addr_c, local_peer_addr_a, 
                                          remote_peer_addr, local_peer_addr_g, 
                                          hashes, payload, local_peer_addr, 
                                          inventory, c, block_data, 
                                          remote_peer_addr_, local_peer_addr_, 
                                          local_peer_addr_M, 
                                          remote_peer_addr_M >>

build_inventory_message(self) == ProcessForInventory(self)
                                    \/ InventoryMessage(self)

GetDataMessage(self) == /\ pc[self] = "GetDataMessage"
                        /\ message_header' =               [
                                             start_string |-> "f9beb4d9",
                                             command_name |-> "getdata",
                                             payload_size |-> payload[self].count,
                                             checksum |-> "0x5df6e0e2"]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ payload' = [payload EXCEPT ![self] = Head(stack[self]).payload]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        message_payload, remote_peer_addr_c, 
                                        local_peer_addr_c, local_peer_addr_a, 
                                        remote_peer_addr, local_peer_addr_g, 
                                        hashes, found_blocks, blocks, hashes_, 
                                        block_headers, local_peer_addr, 
                                        inventory, c, block_data, 
                                        remote_peer_addr_, local_peer_addr_, 
                                        local_peer_addr_M, remote_peer_addr_M >>

process_inventory_message(self) == GetDataMessage(self)

IncorporateLoop(self) == /\ pc[self] = "IncorporateLoop"
                         /\ IF c[self] <= Len(message_payload.inventory)
                               THEN /\ block_data' = [block_data EXCEPT ![self] = FindBlockByHash(selected_remote_peer.blocks, message_payload.inventory[c[self]].hash)]
                                    /\ Assert(block_data'[self].hash = message_payload.inventory[c[self]].hash, 
                                              "Failure of assertion at line 172, column 13.")
                                    /\ the_network' =                UpdatePeerBlocks(local_peer_addr[self], [
                                                          height |-> block_data'[self].height,
                                                          hash |-> block_data'[self].hash,
                                                          block |-> block_data'[self].block
                                                      ])
                                    /\ c' = [c EXCEPT ![self] = c[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                                    /\ UNCHANGED << stack, local_peer_addr, 
                                                    inventory >>
                               ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                                    /\ block_data' = [block_data EXCEPT ![self] = Head(stack[self]).block_data]
                                    /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = Head(stack[self]).local_peer_addr]
                                    /\ inventory' = [inventory EXCEPT ![self] = Head(stack[self]).inventory]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED the_network
                         /\ UNCHANGED << selected_remote_peer, message_header, 
                                         message_payload, remote_peer_addr_c, 
                                         local_peer_addr_c, local_peer_addr_a, 
                                         remote_peer_addr, local_peer_addr_g, 
                                         hashes, found_blocks, blocks, hashes_, 
                                         block_headers, payload, 
                                         remote_peer_addr_, local_peer_addr_, 
                                         local_peer_addr_M, remote_peer_addr_M >>

incorporate_data_to_local_peer(self) == IncorporateLoop(self)

WaitForCommand == /\ pc["Peer Client Task"] = "WaitForCommand"
                  /\ IF message_header # defaultInitValue
                        THEN /\ pc' = [pc EXCEPT !["Peer Client Task"] = "Requests"]
                        ELSE /\ pc' = [pc EXCEPT !["Peer Client Task"] = "WaitForCommand"]
                  /\ UNCHANGED << the_network, selected_remote_peer, 
                                  message_header, message_payload, stack, 
                                  remote_peer_addr_c, local_peer_addr_c, 
                                  local_peer_addr_a, remote_peer_addr, 
                                  local_peer_addr_g, hashes, found_blocks, 
                                  blocks, hashes_, block_headers, payload, 
                                  local_peer_addr, inventory, c, block_data, 
                                  remote_peer_addr_, local_peer_addr_, 
                                  local_peer_addr_M, remote_peer_addr_M >>

Requests == /\ pc["Peer Client Task"] = "Requests"
            /\ IF message_header.command_name = "version"
                  THEN /\ local_peer_addr_' = message_payload.addr_recv
                       /\ remote_peer_addr_' = message_payload.addr_trans
                       /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "send_verack",
                                                                              pc        |->  "Requests" ] >>
                                                                          \o stack["Peer Client Task"]]
                       /\ pc' = [pc EXCEPT !["Peer Client Task"] = "VerackMessage"]
                       /\ UNCHANGED << local_peer_addr_a, remote_peer_addr, 
                                       found_blocks, blocks, hashes_, 
                                       block_headers, payload, local_peer_addr, 
                                       inventory, c, block_data >>
                  ELSE /\ IF message_header.command_name = "verack"
                             THEN /\ /\ local_peer_addr_a' = [local_peer_addr_a EXCEPT !["Peer Client Task"] = local_peer_addr_]
                                     /\ remote_peer_addr' = [remote_peer_addr EXCEPT !["Peer Client Task"] = remote_peer_addr_]
                                     /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "append_peer_to_the_network",
                                                                                            pc        |->  "ClientTaskLoop",
                                                                                            local_peer_addr_a |->  local_peer_addr_a["Peer Client Task"],
                                                                                            remote_peer_addr |->  remote_peer_addr["Peer Client Task"] ] >>
                                                                                        \o stack["Peer Client Task"]]
                                  /\ pc' = [pc EXCEPT !["Peer Client Task"] = "AppendPeerToTheNetwork"]
                                  /\ UNCHANGED << found_blocks, blocks, 
                                                  hashes_, block_headers, 
                                                  payload, local_peer_addr, 
                                                  inventory, c, block_data >>
                             ELSE /\ IF message_header.command_name = "getblocks"
                                        THEN /\ /\ found_blocks' = [found_blocks EXCEPT !["Peer Client Task"] = FindBlocks(selected_remote_peer.blocks, 1, MaxGetBlocksInvResponse)]
                                                /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "build_inventory_message",
                                                                                                       pc        |->  "Requests",
                                                                                                       blocks    |->  blocks["Peer Client Task"],
                                                                                                       hashes_   |->  hashes_["Peer Client Task"],
                                                                                                       block_headers |->  block_headers["Peer Client Task"],
                                                                                                       found_blocks |->  found_blocks["Peer Client Task"] ] >>
                                                                                                   \o stack["Peer Client Task"]]
                                             /\ blocks' = [blocks EXCEPT !["Peer Client Task"] = defaultInitValue]
                                             /\ hashes_' = [hashes_ EXCEPT !["Peer Client Task"] = defaultInitValue]
                                             /\ block_headers' = [block_headers EXCEPT !["Peer Client Task"] = defaultInitValue]
                                             /\ pc' = [pc EXCEPT !["Peer Client Task"] = "ProcessForInventory"]
                                             /\ UNCHANGED << payload, 
                                                             local_peer_addr, 
                                                             inventory, c, 
                                                             block_data >>
                                        ELSE /\ IF message_header.command_name = "inv"
                                                   THEN /\ /\ payload' = [payload EXCEPT !["Peer Client Task"] = message_payload]
                                                           /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "process_inventory_message",
                                                                                                                  pc        |->  "Requests",
                                                                                                                  payload   |->  payload["Peer Client Task"] ] >>
                                                                                                              \o stack["Peer Client Task"]]
                                                        /\ pc' = [pc EXCEPT !["Peer Client Task"] = "GetDataMessage"]
                                                        /\ UNCHANGED << local_peer_addr, 
                                                                        inventory, 
                                                                        c, 
                                                                        block_data >>
                                                   ELSE /\ IF message_header.command_name = "getdata"
                                                              THEN /\ /\ inventory' = [inventory EXCEPT !["Peer Client Task"] = message_payload.inventory]
                                                                      /\ local_peer_addr' = [local_peer_addr EXCEPT !["Peer Client Task"] = local_peer_addr_]
                                                                      /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "incorporate_data_to_local_peer",
                                                                                                                             pc        |->  "ClientTaskLoop",
                                                                                                                             c         |->  c["Peer Client Task"],
                                                                                                                             block_data |->  block_data["Peer Client Task"],
                                                                                                                             local_peer_addr |->  local_peer_addr["Peer Client Task"],
                                                                                                                             inventory |->  inventory["Peer Client Task"] ] >>
                                                                                                                         \o stack["Peer Client Task"]]
                                                                   /\ c' = [c EXCEPT !["Peer Client Task"] = 1]
                                                                   /\ block_data' = [block_data EXCEPT !["Peer Client Task"] = defaultInitValue]
                                                                   /\ pc' = [pc EXCEPT !["Peer Client Task"] = "IncorporateLoop"]
                                                              ELSE /\ pc' = [pc EXCEPT !["Peer Client Task"] = "ClientTaskLoop"]
                                                                   /\ UNCHANGED << stack, 
                                                                                   local_peer_addr, 
                                                                                   inventory, 
                                                                                   c, 
                                                                                   block_data >>
                                                        /\ UNCHANGED payload
                                             /\ UNCHANGED << found_blocks, 
                                                             blocks, hashes_, 
                                                             block_headers >>
                                  /\ UNCHANGED << local_peer_addr_a, 
                                                  remote_peer_addr >>
                       /\ UNCHANGED << remote_peer_addr_, local_peer_addr_ >>
            /\ UNCHANGED << the_network, selected_remote_peer, message_header, 
                            message_payload, remote_peer_addr_c, 
                            local_peer_addr_c, local_peer_addr_g, hashes, 
                            local_peer_addr_M, remote_peer_addr_M >>

ClientTaskLoop == /\ pc["Peer Client Task"] = "ClientTaskLoop"
                  /\ message_header' = defaultInitValue
                  /\ message_payload' = defaultInitValue
                  /\ pc' = [pc EXCEPT !["Peer Client Task"] = "WaitForCommand"]
                  /\ UNCHANGED << the_network, selected_remote_peer, stack, 
                                  remote_peer_addr_c, local_peer_addr_c, 
                                  local_peer_addr_a, remote_peer_addr, 
                                  local_peer_addr_g, hashes, found_blocks, 
                                  blocks, hashes_, block_headers, payload, 
                                  local_peer_addr, inventory, c, block_data, 
                                  remote_peer_addr_, local_peer_addr_, 
                                  local_peer_addr_M, remote_peer_addr_M >>

client_task == WaitForCommand \/ Requests \/ ClientTaskLoop

Setup == /\ pc["Main"] = "Setup"
         /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "initial_conditions",
                                                    pc        |->  "CreateConnection" ] >>
                                                \o stack["Main"]]
         /\ pc' = [pc EXCEPT !["Main"] = "AddPeer1"]
         /\ UNCHANGED << the_network, selected_remote_peer, message_header, 
                         message_payload, remote_peer_addr_c, 
                         local_peer_addr_c, local_peer_addr_a, 
                         remote_peer_addr, local_peer_addr_g, hashes, 
                         found_blocks, blocks, hashes_, block_headers, payload, 
                         local_peer_addr, inventory, c, block_data, 
                         remote_peer_addr_, local_peer_addr_, 
                         local_peer_addr_M, remote_peer_addr_M >>

CreateConnection == /\ pc["Main"] = "CreateConnection"
                    /\ local_peer_addr_M' = "peer8"
                    /\ remote_peer_addr_M' = "peer1"
                    /\ /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT !["Main"] = local_peer_addr_M']
                       /\ remote_peer_addr_c' = [remote_peer_addr_c EXCEPT !["Main"] = remote_peer_addr_M']
                       /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "create_connection",
                                                                  pc        |->  "SelectPeerForRequestFromLocalPeer",
                                                                  remote_peer_addr_c |->  remote_peer_addr_c["Main"],
                                                                  local_peer_addr_c |->  local_peer_addr_c["Main"] ] >>
                                                              \o stack["Main"]]
                    /\ pc' = [pc EXCEPT !["Main"] = "VersionMessage"]
                    /\ UNCHANGED << the_network, selected_remote_peer, 
                                    message_header, message_payload, 
                                    local_peer_addr_a, remote_peer_addr, 
                                    local_peer_addr_g, hashes, found_blocks, 
                                    blocks, hashes_, block_headers, payload, 
                                    local_peer_addr, inventory, c, block_data, 
                                    remote_peer_addr_, local_peer_addr_ >>

SelectPeerForRequestFromLocalPeer == /\ pc["Main"] = "SelectPeerForRequestFromLocalPeer"
                                     /\ Len(the_network) = 2
                                     /\ /\ local_peer_addr_g' = [local_peer_addr_g EXCEPT !["Main"] = local_peer_addr_M]
                                        /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "get_peer_from_the_network",
                                                                                   pc        |->  "RequestInventory",
                                                                                   local_peer_addr_g |->  local_peer_addr_g["Main"] ] >>
                                                                               \o stack["Main"]]
                                     /\ pc' = [pc EXCEPT !["Main"] = "GetPeerFromTheNetwork"]
                                     /\ UNCHANGED << the_network, 
                                                     selected_remote_peer, 
                                                     message_header, 
                                                     message_payload, 
                                                     remote_peer_addr_c, 
                                                     local_peer_addr_c, 
                                                     local_peer_addr_a, 
                                                     remote_peer_addr, hashes, 
                                                     found_blocks, blocks, 
                                                     hashes_, block_headers, 
                                                     payload, local_peer_addr, 
                                                     inventory, c, block_data, 
                                                     remote_peer_addr_, 
                                                     local_peer_addr_, 
                                                     local_peer_addr_M, 
                                                     remote_peer_addr_M >>

RequestInventory == /\ pc["Main"] = "RequestInventory"
                    /\ /\ hashes' = [hashes EXCEPT !["Main"] = <<>>]
                       /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "request_blocks",
                                                                  pc        |->  "CheckStatus",
                                                                  hashes    |->  hashes["Main"] ] >>
                                                              \o stack["Main"]]
                    /\ pc' = [pc EXCEPT !["Main"] = "GetBlocksMessage"]
                    /\ UNCHANGED << the_network, selected_remote_peer, 
                                    message_header, message_payload, 
                                    remote_peer_addr_c, local_peer_addr_c, 
                                    local_peer_addr_a, remote_peer_addr, 
                                    local_peer_addr_g, found_blocks, blocks, 
                                    hashes_, block_headers, payload, 
                                    local_peer_addr, inventory, c, block_data, 
                                    remote_peer_addr_, local_peer_addr_, 
                                    local_peer_addr_M, remote_peer_addr_M >>

CheckStatus == /\ pc["Main"] = "CheckStatus"
               /\ Cardinality(the_network[1].blocks) = 4
               /\ Cardinality(the_network[2].blocks) = 3
               /\ pc' = [pc EXCEPT !["Main"] = "RequestMoreBlocks"]
               /\ UNCHANGED << the_network, selected_remote_peer, 
                               message_header, message_payload, stack, 
                               remote_peer_addr_c, local_peer_addr_c, 
                               local_peer_addr_a, remote_peer_addr, 
                               local_peer_addr_g, hashes, found_blocks, blocks, 
                               hashes_, block_headers, payload, 
                               local_peer_addr, inventory, c, block_data, 
                               remote_peer_addr_, local_peer_addr_, 
                               local_peer_addr_M, remote_peer_addr_M >>

RequestMoreBlocks == /\ pc["Main"] = "RequestMoreBlocks"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT !["Main"] = "Done"]
                     /\ UNCHANGED << the_network, selected_remote_peer, 
                                     message_header, message_payload, stack, 
                                     remote_peer_addr_c, local_peer_addr_c, 
                                     local_peer_addr_a, remote_peer_addr, 
                                     local_peer_addr_g, hashes, found_blocks, 
                                     blocks, hashes_, block_headers, payload, 
                                     local_peer_addr, inventory, c, block_data, 
                                     remote_peer_addr_, local_peer_addr_, 
                                     local_peer_addr_M, remote_peer_addr_M >>

Main == Setup \/ CreateConnection \/ SelectPeerForRequestFromLocalPeer
           \/ RequestInventory \/ CheckStatus \/ RequestMoreBlocks

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == client_task \/ Main
           \/ (\E self \in ProcSet:  \/ initial_conditions(self)
                                     \/ create_connection(self)
                                     \/ send_verack(self)
                                     \/ append_peer_to_the_network(self)
                                     \/ get_peer_from_the_network(self)
                                     \/ request_blocks(self)
                                     \/ build_inventory_message(self)
                                     \/ process_inventory_message(self)
                                     \/ incorporate_data_to_local_peer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
