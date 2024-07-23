---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils

MaxGetBlocksInvResponse == 3

(*--algorithm p2p

variables
    the_network = <<>>;

    selected_peer;
    local_peer;

    message_header;
    message_payload;
define
    \* Given a block collection and a hash, returns the block with the given hash.
    FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash
    
    \* Updates the blocks of a peer in the network.
    UpdatePeerBlocks(peerName, newBlocks) == [i \in 1..Len(the_network) |-> 
        IF the_network[i].peer = peerName THEN
            [the_network[i] EXCEPT !.blocks = @ \cup {newBlocks}] 
        ELSE
            the_network[i]
    ]

    \* Given a block collection, a start height and an end height, returns the blocks in the given range.
    FindBlocks(block_collection, startHeight, endHeight) == 
        [b \in block_collection |-> b.height >= startHeight /\ b.height <= endHeight]
    
    \* Get the peer set of a peer given a peer name and the network state as a set.
    GetPeerFromNetwork(state, peerName) == CHOOSE rec \in state : rec.peer = peerName
end define;

\* Define initial network conditions, we should have at least 1 peer with some blocks in the network
\* and a local peer address.
procedure initial_conditions() 
begin
    AddPeer1:
        the_network := Append(the_network, [peer |-> "peer1", blocks |-> {
            [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
            [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
            [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
            [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"]
        }, peer_set |-> {}]);
    SetLocalPeer:
        local_peer := "peer8";
        return;
end procedure;

\* Create a connection between the remote and local peer.
procedure create_connection(remote_peer_addr, local_peer_addr)
begin
    ConnectMessage:
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

\* Append a peer to the network.
procedure append_peer_to_the_network(peer, remote_peer)
begin
    AppendPeerToTheNetwork:
        the_network := Append(the_network, [
            peer |-> peer,
            blocks |-> {}, \* empty blocks for now
            peer_set |-> {remote_peer}
        ]);
    return; 
end procedure;

\* Look at the peer set of the local node and get one of the peers we are connected to.
procedure get_peer_from_the_network()
begin
    GetPeerFromTheNetwork:
        \* The network should have at least 2 peers to make this work.
        await Len(the_network) >= 2;
        \* Get network data of a peer from the local peer set.
        \* TODO: I am unsure if i can get the full data of the remote peer here or just the name.
        selected_peer := GetPeerFromNetwork(
            ToSet(the_network),
            CHOOSE peer_set \in GetPeerFromNetwork(ToSet(the_network), local_peer).peer_set : TRUE
        );
        return;
end procedure;

\* Request blocks from the selected peer by sending a getblocks message.
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

\* Build an inventory message to request blocks from the selected peer.
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
procedure incorporate_data_to_local_peer(inventory)
variables 
    block,
    height,
    hash ,
    c = 1,
    block_structure;
begin
    \* Here we are sure the selected peer has the requested blocks.
    IncorporateLoop:
        while c <= Len(message_payload.inventory) do
            block_structure := FindBlockByHash(selected_peer.blocks, message_payload.inventory[c].hash);
            block := block_structure.block;
            height := block_structure.height;
            assert block_structure.hash = message_payload.inventory[c].hash;
            hash := block_structure.hash;
                            
            the_network := UpdatePeerBlocks(local_peer, [height |-> height, hash |-> message_payload.inventory[c].hash, block |-> block]);        
            c := c + 1;
        end while;
    return;
end procedure;

\* Peer Client Task
process client_task = "Peer Client Task"
variables remote_peer;
begin
    Requests:
        if message_header # defaultInitValue then
            Services:
                if message_header.command_name = "version" then
                    remote_peer := message_payload.addr_trans;
                    call send_verack();
                    goto Requests;
                elsif message_header.command_name = "verack" then
                    call append_peer_to_the_network(local_peer, remote_peer);
                elsif message_header.command_name = "getblocks" then
                    call build_inventory_message(FindBlocks(selected_peer.blocks, 1, MaxGetBlocksInvResponse));
                    goto Requests;    
                elsif message_header.command_name = "inv" then
                    call process_inventory_message(message_payload);
                    goto Requests;
                elsif message_header.command_name = "getdata" then
                    call incorporate_data_to_local_peer(message_payload.inventory);
                end if;
        end if;
    ClientTaskLoop:
        message_header := defaultInitValue;
        message_payload := defaultInitValue;
        goto Requests;
end process;

process Main = "Main"
begin
    Setup:
        call initial_conditions();
    CreateConnection:
        assert local_peer # defaultInitValue;
        call create_connection("peer1", local_peer);
    SelectPeerForRequestFromPeer2:
        await Len(the_network) = 2;
        call get_peer_from_the_network();
    RequestInventory:
        call request_blocks(<<>>);
    CheckStatus:
        \* Not in sync yet.
        assert Cardinality(the_network[1].blocks) = 4;
        assert Cardinality(the_network[2].blocks) = 3;
    RequestMoreBlocks:
        \*print(GetPeerFromNetwork(ToSet(the_network), local_peer));
        skip;
        \*call request_blocks(<<"blockhash3">>);
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e36275fd" /\ chksum(tla) = "5b08290b")
\* Process variable remote_peer of process client_task at line 196 col 11 changed to remote_peer_
\* Procedure variable hashes of procedure build_inventory_message at line 140 col 19 changed to hashes_
CONSTANT defaultInitValue
VARIABLES the_network, selected_peer, local_peer, message_header, 
          message_payload, pc, stack

(* define statement *)
FindBlockByHash(block_collection, hash) == CHOOSE b \in block_collection : b.hash = hash


UpdatePeerBlocks(peerName, newBlocks) == [i \in 1..Len(the_network) |->
    IF the_network[i].peer = peerName THEN
        [the_network[i] EXCEPT !.blocks = @ \cup {newBlocks}]
    ELSE
        the_network[i]
]


FindBlocks(block_collection, startHeight, endHeight) ==
    [b \in block_collection |-> b.height >= startHeight /\ b.height <= endHeight]


GetPeerFromNetwork(state, peerName) == CHOOSE rec \in state : rec.peer = peerName

VARIABLES remote_peer_addr, local_peer_addr, peer, remote_peer, hashes, 
          found_blocks, blocks, hashes_, block_headers, payload, inventory, 
          block, height, hash, c, block_structure, remote_peer_

vars == << the_network, selected_peer, local_peer, message_header, 
           message_payload, pc, stack, remote_peer_addr, local_peer_addr, 
           peer, remote_peer, hashes, found_blocks, blocks, hashes_, 
           block_headers, payload, inventory, block, height, hash, c, 
           block_structure, remote_peer_ >>

ProcSet == {"Peer Client Task"} \cup {"Main"}

Init == (* Global variables *)
        /\ the_network = <<>>
        /\ selected_peer = defaultInitValue
        /\ local_peer = defaultInitValue
        /\ message_header = defaultInitValue
        /\ message_payload = defaultInitValue
        (* Procedure create_connection *)
        /\ remote_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ local_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure append_peer_to_the_network *)
        /\ peer = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer = [ self \in ProcSet |-> defaultInitValue]
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
        /\ inventory = [ self \in ProcSet |-> defaultInitValue]
        /\ block = [ self \in ProcSet |-> defaultInitValue]
        /\ height = [ self \in ProcSet |-> defaultInitValue]
        /\ hash = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> 1]
        /\ block_structure = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_task *)
        /\ remote_peer_ = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "Peer Client Task" -> "Requests"
                                        [] self = "Main" -> "Setup"]

AddPeer1(self) == /\ pc[self] = "AddPeer1"
                  /\ the_network' =                Append(the_network, [peer |-> "peer1", blocks |-> {
                                        [height |-> 1, hash |-> "blockhash1", block |-> "serialized block data 1"],
                                        [height |-> 2, hash |-> "blockhash2", block |-> "serialized block data 2"],
                                        [height |-> 3, hash |-> "blockhash3", block |-> "serialized block data 3"],
                                        [height |-> 4, hash |-> "blockhash4", block |-> "serialized block data 4"]
                                    }, peer_set |-> {}])
                  /\ pc' = [pc EXCEPT ![self] = "SetLocalPeer"]
                  /\ UNCHANGED << selected_peer, local_peer, message_header, 
                                  message_payload, stack, remote_peer_addr, 
                                  local_peer_addr, peer, remote_peer, hashes, 
                                  found_blocks, blocks, hashes_, block_headers, 
                                  payload, inventory, block, height, hash, c, 
                                  block_structure, remote_peer_ >>

SetLocalPeer(self) == /\ pc[self] = "SetLocalPeer"
                      /\ local_peer' = "peer8"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << the_network, selected_peer, 
                                      message_header, message_payload, 
                                      remote_peer_addr, local_peer_addr, peer, 
                                      remote_peer, hashes, found_blocks, 
                                      blocks, hashes_, block_headers, payload, 
                                      inventory, block, height, hash, c, 
                                      block_structure, remote_peer_ >>

initial_conditions(self) == AddPeer1(self) \/ SetLocalPeer(self)

ConnectMessage(self) == /\ pc[self] = "ConnectMessage"
                        /\ message_header' =               [
                                             start_string |-> "f9beb4d9",
                                             command_name |-> "version",
                                             payload_size |-> 1,
                                             checksum |-> "0x5df6e0e2"]
                        /\ message_payload' =                [
                                              version |-> "70015",
                                              services |-> "0x01",
                                              timestamp |-> "",
                                              addr_recv |-> local_peer_addr[self],
                                              addr_trans |-> remote_peer_addr[self],
                                              nonce |-> "",
                                              user_agent |-> "",
                                              start_height |-> 0,
                                              relay |-> ""]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = Head(stack[self]).remote_peer_addr]
                        /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = Head(stack[self]).local_peer_addr]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                        peer, remote_peer, hashes, 
                                        found_blocks, blocks, hashes_, 
                                        block_headers, payload, inventory, 
                                        block, height, hash, c, 
                                        block_structure, remote_peer_ >>

create_connection(self) == ConnectMessage(self)

VerackMessage(self) == /\ pc[self] = "VerackMessage"
                       /\ message_header' =               [
                                            start_string |-> "f9beb4d9",
                                            command_name |-> "verack",
                                            payload_size |-> 0,
                                            checksum |-> "0x5df6e0e2"]
                       /\ message_payload' = defaultInitValue
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                       remote_peer_addr, local_peer_addr, peer, 
                                       remote_peer, hashes, found_blocks, 
                                       blocks, hashes_, block_headers, payload, 
                                       inventory, block, height, hash, c, 
                                       block_structure, remote_peer_ >>

send_verack(self) == VerackMessage(self)

AppendPeerToTheNetwork(self) == /\ pc[self] = "AppendPeerToTheNetwork"
                                /\ the_network' =                Append(the_network, [
                                                      peer |-> peer[self],
                                                      blocks |-> {},
                                                      peer_set |-> {remote_peer[self]}
                                                  ])
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ peer' = [peer EXCEPT ![self] = Head(stack[self]).peer]
                                /\ remote_peer' = [remote_peer EXCEPT ![self] = Head(stack[self]).remote_peer]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << selected_peer, local_peer, 
                                                message_header, 
                                                message_payload, 
                                                remote_peer_addr, 
                                                local_peer_addr, hashes, 
                                                found_blocks, blocks, hashes_, 
                                                block_headers, payload, 
                                                inventory, block, height, hash, 
                                                c, block_structure, 
                                                remote_peer_ >>

append_peer_to_the_network(self) == AppendPeerToTheNetwork(self)

GetPeerFromTheNetwork(self) == /\ pc[self] = "GetPeerFromTheNetwork"
                               /\ Len(the_network) >= 2
                               /\ selected_peer' =                  GetPeerFromNetwork(
                                                       ToSet(the_network),
                                                       CHOOSE peer_set \in GetPeerFromNetwork(ToSet(the_network), local_peer).peer_set : TRUE
                                                   )
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << the_network, local_peer, 
                                               message_header, message_payload, 
                                               remote_peer_addr, 
                                               local_peer_addr, peer, 
                                               remote_peer, hashes, 
                                               found_blocks, blocks, hashes_, 
                                               block_headers, payload, 
                                               inventory, block, height, hash, 
                                               c, block_structure, 
                                               remote_peer_ >>

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
                          /\ UNCHANGED << the_network, selected_peer, 
                                          local_peer, remote_peer_addr, 
                                          local_peer_addr, peer, remote_peer, 
                                          found_blocks, blocks, hashes_, 
                                          block_headers, payload, inventory, 
                                          block, height, hash, c, 
                                          block_structure, remote_peer_ >>

request_blocks(self) == GetBlocksMessage(self)

ProcessForInventory(self) == /\ pc[self] = "ProcessForInventory"
                             /\ blocks' = [blocks EXCEPT ![self] = { r \in DOMAIN found_blocks[self] : found_blocks[self][r] = TRUE }]
                             /\ hashes_' = [hashes_ EXCEPT ![self] = SetToSeq({ s.hash : s \in blocks'[self] })]
                             /\ block_headers' = [block_headers EXCEPT ![self] = [h \in 1..Len(hashes_'[self]) |-> [type_identifier |-> "MSG_BLOCK", hash |-> hashes_'[self][h]]]]
                             /\ pc' = [pc EXCEPT ![self] = "InventoryMessage"]
                             /\ UNCHANGED << the_network, selected_peer, 
                                             local_peer, message_header, 
                                             message_payload, stack, 
                                             remote_peer_addr, local_peer_addr, 
                                             peer, remote_peer, hashes, 
                                             found_blocks, payload, inventory, 
                                             block, height, hash, c, 
                                             block_structure, remote_peer_ >>

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
                          /\ UNCHANGED << the_network, selected_peer, 
                                          local_peer, remote_peer_addr, 
                                          local_peer_addr, peer, remote_peer, 
                                          hashes, payload, inventory, block, 
                                          height, hash, c, block_structure, 
                                          remote_peer_ >>

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
                        /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                        message_payload, remote_peer_addr, 
                                        local_peer_addr, peer, remote_peer, 
                                        hashes, found_blocks, blocks, hashes_, 
                                        block_headers, inventory, block, 
                                        height, hash, c, block_structure, 
                                        remote_peer_ >>

process_inventory_message(self) == GetDataMessage(self)

IncorporateLoop(self) == /\ pc[self] = "IncorporateLoop"
                         /\ IF c[self] <= Len(message_payload.inventory)
                               THEN /\ block_structure' = [block_structure EXCEPT ![self] = FindBlockByHash(selected_peer.blocks, message_payload.inventory[c[self]].hash)]
                                    /\ block' = [block EXCEPT ![self] = block_structure'[self].block]
                                    /\ height' = [height EXCEPT ![self] = block_structure'[self].height]
                                    /\ Assert(block_structure'[self].hash = message_payload.inventory[c[self]].hash, 
                                              "Failure of assertion at line 185, column 13.")
                                    /\ hash' = [hash EXCEPT ![self] = block_structure'[self].hash]
                                    /\ the_network' = UpdatePeerBlocks(local_peer, [height |-> height'[self], hash |-> message_payload.inventory[c[self]].hash, block |-> block'[self]])
                                    /\ c' = [c EXCEPT ![self] = c[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                                    /\ UNCHANGED << stack, inventory >>
                               ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ block' = [block EXCEPT ![self] = Head(stack[self]).block]
                                    /\ height' = [height EXCEPT ![self] = Head(stack[self]).height]
                                    /\ hash' = [hash EXCEPT ![self] = Head(stack[self]).hash]
                                    /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                                    /\ block_structure' = [block_structure EXCEPT ![self] = Head(stack[self]).block_structure]
                                    /\ inventory' = [inventory EXCEPT ![self] = Head(stack[self]).inventory]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED the_network
                         /\ UNCHANGED << selected_peer, local_peer, 
                                         message_header, message_payload, 
                                         remote_peer_addr, local_peer_addr, 
                                         peer, remote_peer, hashes, 
                                         found_blocks, blocks, hashes_, 
                                         block_headers, payload, remote_peer_ >>

incorporate_data_to_local_peer(self) == IncorporateLoop(self)

Requests == /\ pc["Peer Client Task"] = "Requests"
            /\ IF message_header # defaultInitValue
                  THEN /\ pc' = [pc EXCEPT !["Peer Client Task"] = "Services"]
                  ELSE /\ pc' = [pc EXCEPT !["Peer Client Task"] = "ClientTaskLoop"]
            /\ UNCHANGED << the_network, selected_peer, local_peer, 
                            message_header, message_payload, stack, 
                            remote_peer_addr, local_peer_addr, peer, 
                            remote_peer, hashes, found_blocks, blocks, hashes_, 
                            block_headers, payload, inventory, block, height, 
                            hash, c, block_structure, remote_peer_ >>

Services == /\ pc["Peer Client Task"] = "Services"
            /\ IF message_header.command_name = "version"
                  THEN /\ remote_peer_' = message_payload.addr_trans
                       /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "send_verack",
                                                                              pc        |->  "Requests" ] >>
                                                                          \o stack["Peer Client Task"]]
                       /\ pc' = [pc EXCEPT !["Peer Client Task"] = "VerackMessage"]
                       /\ UNCHANGED << peer, remote_peer, found_blocks, blocks, 
                                       hashes_, block_headers, payload, 
                                       inventory, block, height, hash, c, 
                                       block_structure >>
                  ELSE /\ IF message_header.command_name = "verack"
                             THEN /\ /\ peer' = [peer EXCEPT !["Peer Client Task"] = local_peer]
                                     /\ remote_peer' = [remote_peer EXCEPT !["Peer Client Task"] = remote_peer_]
                                     /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "append_peer_to_the_network",
                                                                                            pc        |->  "ClientTaskLoop",
                                                                                            peer      |->  peer["Peer Client Task"],
                                                                                            remote_peer |->  remote_peer["Peer Client Task"] ] >>
                                                                                        \o stack["Peer Client Task"]]
                                  /\ pc' = [pc EXCEPT !["Peer Client Task"] = "AppendPeerToTheNetwork"]
                                  /\ UNCHANGED << found_blocks, blocks, 
                                                  hashes_, block_headers, 
                                                  payload, inventory, block, 
                                                  height, hash, c, 
                                                  block_structure >>
                             ELSE /\ IF message_header.command_name = "getblocks"
                                        THEN /\ /\ found_blocks' = [found_blocks EXCEPT !["Peer Client Task"] = FindBlocks(selected_peer.blocks, 1, MaxGetBlocksInvResponse)]
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
                                                             inventory, block, 
                                                             height, hash, c, 
                                                             block_structure >>
                                        ELSE /\ IF message_header.command_name = "inv"
                                                   THEN /\ /\ payload' = [payload EXCEPT !["Peer Client Task"] = message_payload]
                                                           /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "process_inventory_message",
                                                                                                                  pc        |->  "Requests",
                                                                                                                  payload   |->  payload["Peer Client Task"] ] >>
                                                                                                              \o stack["Peer Client Task"]]
                                                        /\ pc' = [pc EXCEPT !["Peer Client Task"] = "GetDataMessage"]
                                                        /\ UNCHANGED << inventory, 
                                                                        block, 
                                                                        height, 
                                                                        hash, 
                                                                        c, 
                                                                        block_structure >>
                                                   ELSE /\ IF message_header.command_name = "getdata"
                                                              THEN /\ /\ inventory' = [inventory EXCEPT !["Peer Client Task"] = message_payload.inventory]
                                                                      /\ stack' = [stack EXCEPT !["Peer Client Task"] = << [ procedure |->  "incorporate_data_to_local_peer",
                                                                                                                             pc        |->  "ClientTaskLoop",
                                                                                                                             block     |->  block["Peer Client Task"],
                                                                                                                             height    |->  height["Peer Client Task"],
                                                                                                                             hash      |->  hash["Peer Client Task"],
                                                                                                                             c         |->  c["Peer Client Task"],
                                                                                                                             block_structure |->  block_structure["Peer Client Task"],
                                                                                                                             inventory |->  inventory["Peer Client Task"] ] >>
                                                                                                                         \o stack["Peer Client Task"]]
                                                                   /\ block' = [block EXCEPT !["Peer Client Task"] = defaultInitValue]
                                                                   /\ height' = [height EXCEPT !["Peer Client Task"] = defaultInitValue]
                                                                   /\ hash' = [hash EXCEPT !["Peer Client Task"] = defaultInitValue]
                                                                   /\ c' = [c EXCEPT !["Peer Client Task"] = 1]
                                                                   /\ block_structure' = [block_structure EXCEPT !["Peer Client Task"] = defaultInitValue]
                                                                   /\ pc' = [pc EXCEPT !["Peer Client Task"] = "IncorporateLoop"]
                                                              ELSE /\ pc' = [pc EXCEPT !["Peer Client Task"] = "ClientTaskLoop"]
                                                                   /\ UNCHANGED << stack, 
                                                                                   inventory, 
                                                                                   block, 
                                                                                   height, 
                                                                                   hash, 
                                                                                   c, 
                                                                                   block_structure >>
                                                        /\ UNCHANGED payload
                                             /\ UNCHANGED << found_blocks, 
                                                             blocks, hashes_, 
                                                             block_headers >>
                                  /\ UNCHANGED << peer, remote_peer >>
                       /\ UNCHANGED remote_peer_
            /\ UNCHANGED << the_network, selected_peer, local_peer, 
                            message_header, message_payload, remote_peer_addr, 
                            local_peer_addr, hashes >>

ClientTaskLoop == /\ pc["Peer Client Task"] = "ClientTaskLoop"
                  /\ message_header' = defaultInitValue
                  /\ message_payload' = defaultInitValue
                  /\ pc' = [pc EXCEPT !["Peer Client Task"] = "Requests"]
                  /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                  stack, remote_peer_addr, local_peer_addr, 
                                  peer, remote_peer, hashes, found_blocks, 
                                  blocks, hashes_, block_headers, payload, 
                                  inventory, block, height, hash, c, 
                                  block_structure, remote_peer_ >>

client_task == Requests \/ Services \/ ClientTaskLoop

Setup == /\ pc["Main"] = "Setup"
         /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "initial_conditions",
                                                    pc        |->  "CreateConnection" ] >>
                                                \o stack["Main"]]
         /\ pc' = [pc EXCEPT !["Main"] = "AddPeer1"]
         /\ UNCHANGED << the_network, selected_peer, local_peer, 
                         message_header, message_payload, remote_peer_addr, 
                         local_peer_addr, peer, remote_peer, hashes, 
                         found_blocks, blocks, hashes_, block_headers, payload, 
                         inventory, block, height, hash, c, block_structure, 
                         remote_peer_ >>

CreateConnection == /\ pc["Main"] = "CreateConnection"
                    /\ Assert(local_peer # defaultInitValue, 
                              "Failure of assertion at line 228, column 9.")
                    /\ /\ local_peer_addr' = [local_peer_addr EXCEPT !["Main"] = local_peer]
                       /\ remote_peer_addr' = [remote_peer_addr EXCEPT !["Main"] = "peer1"]
                       /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "create_connection",
                                                                  pc        |->  "SelectPeerForRequestFromPeer2",
                                                                  remote_peer_addr |->  remote_peer_addr["Main"],
                                                                  local_peer_addr |->  local_peer_addr["Main"] ] >>
                                                              \o stack["Main"]]
                    /\ pc' = [pc EXCEPT !["Main"] = "ConnectMessage"]
                    /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                    message_header, message_payload, peer, 
                                    remote_peer, hashes, found_blocks, blocks, 
                                    hashes_, block_headers, payload, inventory, 
                                    block, height, hash, c, block_structure, 
                                    remote_peer_ >>

SelectPeerForRequestFromPeer2 == /\ pc["Main"] = "SelectPeerForRequestFromPeer2"
                                 /\ Len(the_network) = 2
                                 /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "get_peer_from_the_network",
                                                                            pc        |->  "RequestInventory" ] >>
                                                                        \o stack["Main"]]
                                 /\ pc' = [pc EXCEPT !["Main"] = "GetPeerFromTheNetwork"]
                                 /\ UNCHANGED << the_network, selected_peer, 
                                                 local_peer, message_header, 
                                                 message_payload, 
                                                 remote_peer_addr, 
                                                 local_peer_addr, peer, 
                                                 remote_peer, hashes, 
                                                 found_blocks, blocks, hashes_, 
                                                 block_headers, payload, 
                                                 inventory, block, height, 
                                                 hash, c, block_structure, 
                                                 remote_peer_ >>

RequestInventory == /\ pc["Main"] = "RequestInventory"
                    /\ /\ hashes' = [hashes EXCEPT !["Main"] = <<>>]
                       /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "request_blocks",
                                                                  pc        |->  "CheckStatus",
                                                                  hashes    |->  hashes["Main"] ] >>
                                                              \o stack["Main"]]
                    /\ pc' = [pc EXCEPT !["Main"] = "GetBlocksMessage"]
                    /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                    message_header, message_payload, 
                                    remote_peer_addr, local_peer_addr, peer, 
                                    remote_peer, found_blocks, blocks, hashes_, 
                                    block_headers, payload, inventory, block, 
                                    height, hash, c, block_structure, 
                                    remote_peer_ >>

CheckStatus == /\ pc["Main"] = "CheckStatus"
               /\ Assert(Cardinality(the_network[1].blocks) = 4, 
                         "Failure of assertion at line 236, column 9.")
               /\ Cardinality(the_network[2].blocks) = 3
               /\ pc' = [pc EXCEPT !["Main"] = "RequestMoreBlocks"]
               /\ UNCHANGED << the_network, selected_peer, local_peer, 
                               message_header, message_payload, stack, 
                               remote_peer_addr, local_peer_addr, peer, 
                               remote_peer, hashes, found_blocks, blocks, 
                               hashes_, block_headers, payload, inventory, 
                               block, height, hash, c, block_structure, 
                               remote_peer_ >>

RequestMoreBlocks == /\ pc["Main"] = "RequestMoreBlocks"
                     /\ PrintT((GetPeerFromNetwork(ToSet(the_network), local_peer)))
                     /\ pc' = [pc EXCEPT !["Main"] = "Done"]
                     /\ UNCHANGED << the_network, selected_peer, local_peer, 
                                     message_header, message_payload, stack, 
                                     remote_peer_addr, local_peer_addr, peer, 
                                     remote_peer, hashes, found_blocks, blocks, 
                                     hashes_, block_headers, payload, 
                                     inventory, block, height, hash, c, 
                                     block_structure, remote_peer_ >>

Main == Setup \/ CreateConnection \/ SelectPeerForRequestFromPeer2
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
