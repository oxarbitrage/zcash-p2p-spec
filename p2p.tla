---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils, Blockchain

MaxGetBlocksInvResponse == 3

MAX_PEERS == 2

IDENTIFIER_DIFFERENCE_OF_PROCESSES == 1000

(*--algorithm p2p

variables
    the_network = Reverse(SetToSeq(PEERS));

    selected_remote_peer = defaultInitValue;

    channels = <<
        [header |-> defaultInitValue, payload |-> defaultInitValue],
        [header |-> defaultInitValue, payload |-> defaultInitValue],
        [header |-> defaultInitValue, payload |-> defaultInitValue]>>;
define
    LOCAL Ops == INSTANCE Operators
end define;

\* Create a connection between the remote and local peer.
procedure create_connection(remote_peer_addr, local_peer_addr, id)
begin
    VersionMessage:
        \* Version messages are sent from the remote transmitting node to the local receiver node:
        \* > The "version" message provides information about the transmitting node to the receiving node
        \* > at the beginning of a connection."
        \* https://developer.bitcoin.org/reference/p2p_networking.html#version

        \* Create a version message and put it into the right channel.
        channels[id] := [
            header |-> [
                start_string |-> "f9beb4d9",
                command_name |-> "version",
                payload_size |-> 1,
                checksum |-> "0x5df6e0e2"],
            payload |-> [
                version |-> "70015",
                services |-> "0x01",
                timestamp |-> "",
                addr_recv |-> local_peer_addr,
                addr_trans |-> remote_peer_addr,
                nonce |-> "",
                user_agent |-> "",
                start_height |-> Ops!GetPeerFromNetwork(remote_peer_addr).chain_tip.height,
                relay |-> ""]
        ];
    return;
end procedure;

\* Send a verack message to the remote peer.
procedure send_verack()
begin
    VerackMessage:
        channels[self] := [
            header |-> [
                start_string |-> "f9beb4d9",
                command_name |-> "verack", 
                payload_size |-> 0,
                checksum |-> "0x5df6e0e2"],
            payload |-> defaultInitValue
        ];
    return;
end procedure;

\* Request blocks from the selected remote peer by sending a getblocks message.
procedure request_blocks(hashes, id)
begin
    GetBlocksMessage:
        channels[id] := [
            header |-> [
                start_string |-> "f9beb4d9",
                command_name |-> "getblocks", 
                payload_size |-> 1,
                checksum |-> "0x5df6e0e2"],
            payload |-> [
                version |-> "70015",
                \* TODO: Here we should send the last hash the local peer has.
                hash_count |-> Len(hashes),
                block_header_hashes |-> hashes,
                stop_hash |-> "0"]
        ];
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
        channels[self] := [
            header |-> [
                start_string |-> "f9beb4d9",
                command_name |-> "inv", 
                payload_size |-> 1,
                checksum |-> "0x5df6e0e2"],
            payload |-> [
                count |-> Len(block_headers),
                inventory |-> block_headers]
        ];
    return;
end procedure;

\* Build getdata messages with the inventory received.
procedure process_inventory_message()
begin
    GetDataMessage:
        \* Validate the inventory? For now we just pass it as it came so we just change the global message header.
        channels[self].header := [
            start_string |-> "f9beb4d9",
            command_name |-> "getdata", 
            payload_size |-> channels[self].payload.count,
            checksum |-> "0x5df6e0e2"];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure incorporate_data_to_local_peer(local_peer_addr, inventory)
variables c = 1, block_data;
begin
    \* Here we are sure the selected peer has the requested blocks.
    IncorporateLoop:
        while c <= Len(channels[self].payload.inventory) do
            block_data := Ops!FindBlockByHash(selected_remote_peer.blocks, channels[self].payload.inventory[c].hash);
            assert block_data.hash = channels[self].payload.inventory[c].hash;
                            
            the_network := Ops!UpdatePeerBlocks(local_peer_addr, [
                height |-> block_data.height,
                hash |-> block_data.hash,
                block |-> block_data.block
            ]);        
            c := c + 1;
        end while;
    UpdateTip: 
        the_network := Ops!UpdatePeerTip(local_peer_addr, [height |-> block_data.height, hash |-> block_data.hash]);
    return;
end procedure;

\* Peer Client Task
process client_task \in 1..MAX_PEERS
variables remote_peer_addr, local_peer_addr, id = self, hash_provided, height_to_start;
begin
    Listening:
        await id > 1;
        await Len(the_network) >= id;
        await Len(channels) >= id;
        if channels[id].header = defaultInitValue then
            goto Listening;
        end if;
    Requests:
        if channels[id].header.command_name = "version" then
            local_peer_addr := channels[id].payload.addr_recv;
            remote_peer_addr := channels[id].payload.addr_trans;
            call send_verack();
            goto Requests;
        elsif channels[id].header.command_name = "verack" then
            \* Add the remote peer to the peer set of the local peer.
            the_network := Ops!UpdatePeerSet(local_peer_addr, remote_peer_addr);
        elsif channels[id].header.command_name = "getblocks" then
            if channels[id].payload.hash_count = 0 then
                \* TODO: This is dirty but correct in some sense, it will build inventory with the 
                \* first `MaxGetBlocksInvResponse` blocks.
                call build_inventory_message(Ops!FindBlocks(selected_remote_peer.blocks, 1, 1 + (MaxGetBlocksInvResponse - 1)));
                goto Requests;
            else
                \* Assuming one block in block header hashes.
                hash_provided := channels[id].payload.block_header_hashes;
                height_to_start := Ops!FindBlockByHash(selected_remote_peer.blocks, hash_provided).height + 1;
                call build_inventory_message(Ops!FindBlocks(selected_remote_peer.blocks, height_to_start, height_to_start + (MaxGetBlocksInvResponse - 1)));
                goto Requests;
            end if;
        elsif channels[id].header.command_name = "inv" then
            call process_inventory_message();
            goto Requests;
        elsif channels[id].header.command_name = "getdata" then
            call incorporate_data_to_local_peer(local_peer_addr, channels[id].payload.inventory);
        end if;
    ClientTaskLoop:
        channels[id] := [header |-> defaultInitValue, payload |-> defaultInitValue];
        goto Listening;
end process;

process Peer \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS)
variables remote_peer_addr, id, remote_peer_height, ignore;
begin
    Connect:
        await Len(the_network) = MAX_PEERS;

        id := self - IDENTIFIER_DIFFERENCE_OF_PROCESSES;

        local_peer_addr := the_network[id].peer;
        remote_peer_addr := "peer1";
        remote_peer_height := the_network[1].chain_tip.height;
    
        \* don't do it for the seeder peer.
        await self > (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1);

        call create_connection(remote_peer_addr, local_peer_addr, id);
    SelectPeerForRequestFromLocalPeer:
        \*  Check connection is established.
        await Cardinality(the_network[id].peer_set) > 0;
        \* Get a peer from the local peer set.
        selected_remote_peer := Ops!GetPeerFromNetwork(
            CHOOSE peer_set \in Ops!GetPeerFromNetwork(local_peer_addr).peer_set : TRUE
        );
    RequestInventory:
        await selected_remote_peer.chain_tip.height > 0;
        await the_network[id].chain_tip.height = 0;
        Sync:
            while the_network[id].chain_tip.height < selected_remote_peer.chain_tip.height do
                await channels[id].header = defaultInitValue;
                await channels[id].payload = defaultInitValue;
                if the_network[id].chain_tip.height = 0 then
                    call request_blocks(<<>>, id);
                else
                    call request_blocks(the_network[id].chain_tip.hash, id);
                end if;
            end while;
    CheckSync:
        await selected_remote_peer.chain_tip.height = the_network[id].chain_tip.height;
        print "Network in sync!";
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "82f5aa00" /\ chksum(tla) = "3d570095")
\* Process variable remote_peer_addr of process client_task at line 154 col 11 changed to remote_peer_addr_
\* Process variable local_peer_addr of process client_task at line 154 col 29 changed to local_peer_addr_
\* Process variable id of process client_task at line 154 col 46 changed to id_
\* Process variable remote_peer_addr of process Peer at line 197 col 11 changed to remote_peer_addr_P
\* Process variable id of process Peer at line 197 col 29 changed to id_P
\* Procedure variable hashes of procedure build_inventory_message at line 92 col 19 changed to hashes_
\* Parameter local_peer_addr of procedure create_connection at line 26 col 47 changed to local_peer_addr_c
\* Parameter id of procedure create_connection at line 26 col 64 changed to id_c
CONSTANT defaultInitValue
VARIABLES the_network, selected_remote_peer, channels, pc, stack

(* define statement *)
LOCAL Ops == INSTANCE Operators

VARIABLES remote_peer_addr, local_peer_addr_c, id_c, hashes, id, found_blocks, 
          blocks, hashes_, block_headers, local_peer_addr, inventory, c, 
          block_data, remote_peer_addr_, local_peer_addr_, id_, hash_provided, 
          height_to_start, remote_peer_addr_P, id_P, remote_peer_height, 
          ignore

vars == << the_network, selected_remote_peer, channels, pc, stack, 
           remote_peer_addr, local_peer_addr_c, id_c, hashes, id, 
           found_blocks, blocks, hashes_, block_headers, local_peer_addr, 
           inventory, c, block_data, remote_peer_addr_, local_peer_addr_, id_, 
           hash_provided, height_to_start, remote_peer_addr_P, id_P, 
           remote_peer_height, ignore >>

ProcSet == (1..MAX_PEERS) \cup ((IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS))

Init == (* Global variables *)
        /\ the_network = Reverse(SetToSeq(PEERS))
        /\ selected_remote_peer = defaultInitValue
        /\ channels =        <<
                      [header |-> defaultInitValue, payload |-> defaultInitValue],
                      [header |-> defaultInitValue, payload |-> defaultInitValue],
                      [header |-> defaultInitValue, payload |-> defaultInitValue]>>
        (* Procedure create_connection *)
        /\ remote_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ local_peer_addr_c = [ self \in ProcSet |-> defaultInitValue]
        /\ id_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
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
        /\ id_ = [self \in 1..MAX_PEERS |-> self]
        /\ hash_provided = [self \in 1..MAX_PEERS |-> defaultInitValue]
        /\ height_to_start = [self \in 1..MAX_PEERS |-> defaultInitValue]
        (* Process Peer *)
        /\ remote_peer_addr_P = [self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) |-> defaultInitValue]
        /\ id_P = [self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) |-> defaultInitValue]
        /\ remote_peer_height = [self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) |-> defaultInitValue]
        /\ ignore = [self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..MAX_PEERS -> "Listening"
                                        [] self \in (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)..(IDENTIFIER_DIFFERENCE_OF_PROCESSES + MAX_PEERS) -> "Connect"]

VersionMessage(self) == /\ pc[self] = "VersionMessage"
                        /\ channels' = [channels EXCEPT ![id_c[self]] =                 [
                                                                            header |-> [
                                                                                start_string |-> "f9beb4d9",
                                                                                command_name |-> "version",
                                                                                payload_size |-> 1,
                                                                                checksum |-> "0x5df6e0e2"],
                                                                            payload |-> [
                                                                                version |-> "70015",
                                                                                services |-> "0x01",
                                                                                timestamp |-> "",
                                                                                addr_recv |-> local_peer_addr_c[self],
                                                                                addr_trans |-> remote_peer_addr[self],
                                                                                nonce |-> "",
                                                                                user_agent |-> "",
                                                                                start_height |-> Ops!GetPeerFromNetwork(remote_peer_addr[self]).chain_tip.height,
                                                                                relay |-> ""]
                                                                        ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = Head(stack[self]).remote_peer_addr]
                        /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT ![self] = Head(stack[self]).local_peer_addr_c]
                        /\ id_c' = [id_c EXCEPT ![self] = Head(stack[self]).id_c]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        hashes, id, found_blocks, blocks, 
                                        hashes_, block_headers, 
                                        local_peer_addr, inventory, c, 
                                        block_data, remote_peer_addr_, 
                                        local_peer_addr_, id_, hash_provided, 
                                        height_to_start, remote_peer_addr_P, 
                                        id_P, remote_peer_height, ignore >>

create_connection(self) == VersionMessage(self)

VerackMessage(self) == /\ pc[self] = "VerackMessage"
                       /\ channels' = [channels EXCEPT ![self] =                   [
                                                                     header |-> [
                                                                         start_string |-> "f9beb4d9",
                                                                         command_name |-> "verack",
                                                                         payload_size |-> 0,
                                                                         checksum |-> "0x5df6e0e2"],
                                                                     payload |-> defaultInitValue
                                                                 ]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << the_network, selected_remote_peer, 
                                       remote_peer_addr, local_peer_addr_c, 
                                       id_c, hashes, id, found_blocks, blocks, 
                                       hashes_, block_headers, local_peer_addr, 
                                       inventory, c, block_data, 
                                       remote_peer_addr_, local_peer_addr_, 
                                       id_, hash_provided, height_to_start, 
                                       remote_peer_addr_P, id_P, 
                                       remote_peer_height, ignore >>

send_verack(self) == VerackMessage(self)

GetBlocksMessage(self) == /\ pc[self] = "GetBlocksMessage"
                          /\ channels' = [channels EXCEPT ![id[self]] =                 [
                                                                            header |-> [
                                                                                start_string |-> "f9beb4d9",
                                                                                command_name |-> "getblocks",
                                                                                payload_size |-> 1,
                                                                                checksum |-> "0x5df6e0e2"],
                                                                            payload |-> [
                                                                                version |-> "70015",
                                                                        
                                                                                hash_count |-> Len(hashes[self]),
                                                                                block_header_hashes |-> hashes[self],
                                                                                stop_hash |-> "0"]
                                                                        ]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ hashes' = [hashes EXCEPT ![self] = Head(stack[self]).hashes]
                          /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          remote_peer_addr, local_peer_addr_c, 
                                          id_c, found_blocks, blocks, hashes_, 
                                          block_headers, local_peer_addr, 
                                          inventory, c, block_data, 
                                          remote_peer_addr_, local_peer_addr_, 
                                          id_, hash_provided, height_to_start, 
                                          remote_peer_addr_P, id_P, 
                                          remote_peer_height, ignore >>

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
                                             channels, stack, remote_peer_addr, 
                                             local_peer_addr_c, id_c, hashes, 
                                             id, found_blocks, local_peer_addr, 
                                             inventory, c, block_data, 
                                             remote_peer_addr_, 
                                             local_peer_addr_, id_, 
                                             hash_provided, height_to_start, 
                                             remote_peer_addr_P, id_P, 
                                             remote_peer_height, ignore >>

InventoryMessage(self) == /\ pc[self] = "InventoryMessage"
                          /\ channels' = [channels EXCEPT ![self] =                   [
                                                                        header |-> [
                                                                            start_string |-> "f9beb4d9",
                                                                            command_name |-> "inv",
                                                                            payload_size |-> 1,
                                                                            checksum |-> "0x5df6e0e2"],
                                                                        payload |-> [
                                                                            count |-> Len(block_headers[self]),
                                                                            inventory |-> block_headers[self]]
                                                                    ]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ blocks' = [blocks EXCEPT ![self] = Head(stack[self]).blocks]
                          /\ hashes_' = [hashes_ EXCEPT ![self] = Head(stack[self]).hashes_]
                          /\ block_headers' = [block_headers EXCEPT ![self] = Head(stack[self]).block_headers]
                          /\ found_blocks' = [found_blocks EXCEPT ![self] = Head(stack[self]).found_blocks]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          remote_peer_addr, local_peer_addr_c, 
                                          id_c, hashes, id, local_peer_addr, 
                                          inventory, c, block_data, 
                                          remote_peer_addr_, local_peer_addr_, 
                                          id_, hash_provided, height_to_start, 
                                          remote_peer_addr_P, id_P, 
                                          remote_peer_height, ignore >>

build_inventory_message(self) == ProcessForInventory(self)
                                    \/ InventoryMessage(self)

GetDataMessage(self) == /\ pc[self] = "GetDataMessage"
                        /\ channels' = [channels EXCEPT ![self].header =                      [
                                                                         start_string |-> "f9beb4d9",
                                                                         command_name |-> "getdata",
                                                                         payload_size |-> channels[self].payload.count,
                                                                         checksum |-> "0x5df6e0e2"]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        remote_peer_addr, local_peer_addr_c, 
                                        id_c, hashes, id, found_blocks, blocks, 
                                        hashes_, block_headers, 
                                        local_peer_addr, inventory, c, 
                                        block_data, remote_peer_addr_, 
                                        local_peer_addr_, id_, hash_provided, 
                                        height_to_start, remote_peer_addr_P, 
                                        id_P, remote_peer_height, ignore >>

process_inventory_message(self) == GetDataMessage(self)

IncorporateLoop(self) == /\ pc[self] = "IncorporateLoop"
                         /\ IF c[self] <= Len(channels[self].payload.inventory)
                               THEN /\ block_data' = [block_data EXCEPT ![self] = Ops!FindBlockByHash(selected_remote_peer.blocks, channels[self].payload.inventory[c[self]].hash)]
                                    /\ Assert(block_data'[self].hash = channels[self].payload.inventory[c[self]].hash, 
                                              "Failure of assertion at line 138, column 13.")
                                    /\ the_network' =                Ops!UpdatePeerBlocks(local_peer_addr[self], [
                                                          height |-> block_data'[self].height,
                                                          hash |-> block_data'[self].hash,
                                                          block |-> block_data'[self].block
                                                      ])
                                    /\ c' = [c EXCEPT ![self] = c[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateTip"]
                                    /\ UNCHANGED << the_network, c, block_data >>
                         /\ UNCHANGED << selected_remote_peer, channels, stack, 
                                         remote_peer_addr, local_peer_addr_c, 
                                         id_c, hashes, id, found_blocks, 
                                         blocks, hashes_, block_headers, 
                                         local_peer_addr, inventory, 
                                         remote_peer_addr_, local_peer_addr_, 
                                         id_, hash_provided, height_to_start, 
                                         remote_peer_addr_P, id_P, 
                                         remote_peer_height, ignore >>

UpdateTip(self) == /\ pc[self] = "UpdateTip"
                   /\ the_network' = Ops!UpdatePeerTip(local_peer_addr[self], [height |-> block_data[self].height, hash |-> block_data[self].hash])
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                   /\ block_data' = [block_data EXCEPT ![self] = Head(stack[self]).block_data]
                   /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = Head(stack[self]).local_peer_addr]
                   /\ inventory' = [inventory EXCEPT ![self] = Head(stack[self]).inventory]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << selected_remote_peer, channels, 
                                   remote_peer_addr, local_peer_addr_c, id_c, 
                                   hashes, id, found_blocks, blocks, hashes_, 
                                   block_headers, remote_peer_addr_, 
                                   local_peer_addr_, id_, hash_provided, 
                                   height_to_start, remote_peer_addr_P, id_P, 
                                   remote_peer_height, ignore >>

incorporate_data_to_local_peer(self) == IncorporateLoop(self)
                                           \/ UpdateTip(self)

Listening(self) == /\ pc[self] = "Listening"
                   /\ id_[self] > 1
                   /\ Len(the_network) >= id_[self]
                   /\ Len(channels) >= id_[self]
                   /\ IF channels[id_[self]].header = defaultInitValue
                         THEN /\ pc' = [pc EXCEPT ![self] = "Listening"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Requests"]
                   /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                                   stack, remote_peer_addr, local_peer_addr_c, 
                                   id_c, hashes, id, found_blocks, blocks, 
                                   hashes_, block_headers, local_peer_addr, 
                                   inventory, c, block_data, remote_peer_addr_, 
                                   local_peer_addr_, id_, hash_provided, 
                                   height_to_start, remote_peer_addr_P, id_P, 
                                   remote_peer_height, ignore >>

Requests(self) == /\ pc[self] = "Requests"
                  /\ IF channels[id_[self]].header.command_name = "version"
                        THEN /\ local_peer_addr_' = [local_peer_addr_ EXCEPT ![self] = channels[id_[self]].payload.addr_recv]
                             /\ remote_peer_addr_' = [remote_peer_addr_ EXCEPT ![self] = channels[id_[self]].payload.addr_trans]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_verack",
                                                                      pc        |->  "Requests" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "VerackMessage"]
                             /\ UNCHANGED << the_network, found_blocks, blocks, 
                                             hashes_, block_headers, 
                                             local_peer_addr, inventory, c, 
                                             block_data, hash_provided, 
                                             height_to_start >>
                        ELSE /\ IF channels[id_[self]].header.command_name = "verack"
                                   THEN /\ the_network' = Ops!UpdatePeerSet(local_peer_addr_[self], remote_peer_addr_[self])
                                        /\ pc' = [pc EXCEPT ![self] = "ClientTaskLoop"]
                                        /\ UNCHANGED << stack, found_blocks, 
                                                        blocks, hashes_, 
                                                        block_headers, 
                                                        local_peer_addr, 
                                                        inventory, c, 
                                                        block_data, 
                                                        hash_provided, 
                                                        height_to_start >>
                                   ELSE /\ IF channels[id_[self]].header.command_name = "getblocks"
                                              THEN /\ IF channels[id_[self]].payload.hash_count = 0
                                                         THEN /\ /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(selected_remote_peer.blocks, 1, 1 + (MaxGetBlocksInvResponse - 1))]
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
                                                              /\ UNCHANGED << hash_provided, 
                                                                              height_to_start >>
                                                         ELSE /\ hash_provided' = [hash_provided EXCEPT ![self] = channels[id_[self]].payload.block_header_hashes]
                                                              /\ height_to_start' = [height_to_start EXCEPT ![self] = Ops!FindBlockByHash(selected_remote_peer.blocks, hash_provided'[self]).height + 1]
                                                              /\ /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(selected_remote_peer.blocks, height_to_start'[self], height_to_start'[self] + (MaxGetBlocksInvResponse - 1))]
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
                                              ELSE /\ IF channels[id_[self]].header.command_name = "inv"
                                                         THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "process_inventory_message",
                                                                                                       pc        |->  "Requests" ] >>
                                                                                                   \o stack[self]]
                                                              /\ pc' = [pc EXCEPT ![self] = "GetDataMessage"]
                                                              /\ UNCHANGED << local_peer_addr, 
                                                                              inventory, 
                                                                              c, 
                                                                              block_data >>
                                                         ELSE /\ IF channels[id_[self]].header.command_name = "getdata"
                                                                    THEN /\ /\ inventory' = [inventory EXCEPT ![self] = channels[id_[self]].payload.inventory]
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
                                                                   block_headers, 
                                                                   hash_provided, 
                                                                   height_to_start >>
                                        /\ UNCHANGED the_network
                             /\ UNCHANGED << remote_peer_addr_, 
                                             local_peer_addr_ >>
                  /\ UNCHANGED << selected_remote_peer, channels, 
                                  remote_peer_addr, local_peer_addr_c, id_c, 
                                  hashes, id, id_, remote_peer_addr_P, id_P, 
                                  remote_peer_height, ignore >>

ClientTaskLoop(self) == /\ pc[self] = "ClientTaskLoop"
                        /\ channels' = [channels EXCEPT ![id_[self]] = [header |-> defaultInitValue, payload |-> defaultInitValue]]
                        /\ pc' = [pc EXCEPT ![self] = "Listening"]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        stack, remote_peer_addr, 
                                        local_peer_addr_c, id_c, hashes, id, 
                                        found_blocks, blocks, hashes_, 
                                        block_headers, local_peer_addr, 
                                        inventory, c, block_data, 
                                        remote_peer_addr_, local_peer_addr_, 
                                        id_, hash_provided, height_to_start, 
                                        remote_peer_addr_P, id_P, 
                                        remote_peer_height, ignore >>

client_task(self) == Listening(self) \/ Requests(self)
                        \/ ClientTaskLoop(self)

Connect(self) == /\ pc[self] = "Connect"
                 /\ Len(the_network) = MAX_PEERS
                 /\ id_P' = [id_P EXCEPT ![self] = self - IDENTIFIER_DIFFERENCE_OF_PROCESSES]
                 /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = the_network[id_P'[self]].peer]
                 /\ remote_peer_addr_P' = [remote_peer_addr_P EXCEPT ![self] = "peer1"]
                 /\ remote_peer_height' = [remote_peer_height EXCEPT ![self] = the_network[1].chain_tip.height]
                 /\ self > (IDENTIFIER_DIFFERENCE_OF_PROCESSES + 1)
                 /\ /\ id_c' = [id_c EXCEPT ![self] = id_P'[self]]
                    /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT ![self] = local_peer_addr'[self]]
                    /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = remote_peer_addr_P'[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "create_connection",
                                                             pc        |->  "SelectPeerForRequestFromLocalPeer",
                                                             remote_peer_addr |->  remote_peer_addr[self],
                                                             local_peer_addr_c |->  local_peer_addr_c[self],
                                                             id_c      |->  id_c[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "VersionMessage"]
                 /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                                 hashes, id, found_blocks, blocks, hashes_, 
                                 block_headers, inventory, c, block_data, 
                                 remote_peer_addr_, local_peer_addr_, id_, 
                                 hash_provided, height_to_start, ignore >>

SelectPeerForRequestFromLocalPeer(self) == /\ pc[self] = "SelectPeerForRequestFromLocalPeer"
                                           /\ Cardinality(the_network[id_P[self]].peer_set) > 0
                                           /\ selected_remote_peer' =                         Ops!GetPeerFromNetwork(
                                                                          CHOOSE peer_set \in Ops!GetPeerFromNetwork(local_peer_addr[self]).peer_set : TRUE
                                                                      )
                                           /\ pc' = [pc EXCEPT ![self] = "RequestInventory"]
                                           /\ UNCHANGED << the_network, 
                                                           channels, stack, 
                                                           remote_peer_addr, 
                                                           local_peer_addr_c, 
                                                           id_c, hashes, id, 
                                                           found_blocks, 
                                                           blocks, hashes_, 
                                                           block_headers, 
                                                           local_peer_addr, 
                                                           inventory, c, 
                                                           block_data, 
                                                           remote_peer_addr_, 
                                                           local_peer_addr_, 
                                                           id_, hash_provided, 
                                                           height_to_start, 
                                                           remote_peer_addr_P, 
                                                           id_P, 
                                                           remote_peer_height, 
                                                           ignore >>

RequestInventory(self) == /\ pc[self] = "RequestInventory"
                          /\ selected_remote_peer.chain_tip.height > 0
                          /\ the_network[id_P[self]].chain_tip.height = 0
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          channels, stack, remote_peer_addr, 
                                          local_peer_addr_c, id_c, hashes, id, 
                                          found_blocks, blocks, hashes_, 
                                          block_headers, local_peer_addr, 
                                          inventory, c, block_data, 
                                          remote_peer_addr_, local_peer_addr_, 
                                          id_, hash_provided, height_to_start, 
                                          remote_peer_addr_P, id_P, 
                                          remote_peer_height, ignore >>

Sync(self) == /\ pc[self] = "Sync"
              /\ IF the_network[id_P[self]].chain_tip.height < selected_remote_peer.chain_tip.height
                    THEN /\ channels[id_P[self]].header = defaultInitValue
                         /\ channels[id_P[self]].payload = defaultInitValue
                         /\ IF the_network[id_P[self]].chain_tip.height = 0
                               THEN /\ /\ hashes' = [hashes EXCEPT ![self] = <<>>]
                                       /\ id' = [id EXCEPT ![self] = id_P[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                pc        |->  "Sync",
                                                                                hashes    |->  hashes[self],
                                                                                id        |->  id[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "GetBlocksMessage"]
                               ELSE /\ /\ hashes' = [hashes EXCEPT ![self] = the_network[id_P[self]].chain_tip.hash]
                                       /\ id' = [id EXCEPT ![self] = id_P[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                pc        |->  "Sync",
                                                                                hashes    |->  hashes[self],
                                                                                id        |->  id[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "GetBlocksMessage"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CheckSync"]
                         /\ UNCHANGED << stack, hashes, id >>
              /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                              remote_peer_addr, local_peer_addr_c, id_c, 
                              found_blocks, blocks, hashes_, block_headers, 
                              local_peer_addr, inventory, c, block_data, 
                              remote_peer_addr_, local_peer_addr_, id_, 
                              hash_provided, height_to_start, 
                              remote_peer_addr_P, id_P, remote_peer_height, 
                              ignore >>

CheckSync(self) == /\ pc[self] = "CheckSync"
                   /\ selected_remote_peer.chain_tip.height = the_network[id_P[self]].chain_tip.height
                   /\ PrintT("Network in sync!")
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                                   stack, remote_peer_addr, local_peer_addr_c, 
                                   id_c, hashes, id, found_blocks, blocks, 
                                   hashes_, block_headers, local_peer_addr, 
                                   inventory, c, block_data, remote_peer_addr_, 
                                   local_peer_addr_, id_, hash_provided, 
                                   height_to_start, remote_peer_addr_P, id_P, 
                                   remote_peer_height, ignore >>

Peer(self) == Connect(self) \/ SelectPeerForRequestFromLocalPeer(self)
                 \/ RequestInventory(self) \/ Sync(self) \/ CheckSync(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ create_connection(self)
                               \/ send_verack(self) \/ request_blocks(self)
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
