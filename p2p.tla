---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils, Blockchain

MaxGetBlocksInvResponse == 3

MAX_PEERS == 2

DIFF_ID == 1000

(*--algorithm p2p

variables
    the_network = SubSeq(Reverse(SetToSeq(PEERS)), 1, MAX_PEERS);

    selected_remote_peer = defaultInitValue;

    channels = [i \in 1..MAX_PEERS |-> [header |-> defaultInitValue, payload |-> defaultInitValue]]
define
    LOCAL Ops == INSTANCE Operators
end define;

\* Create a connection between the remote and local peer.
procedure create_connection(remote_peer_addr, local_peer_addr, id)
begin
    VersionMessage:
        channels[id] := [
            header |-> [command_name |-> "version"],
            payload |-> [
                addr_recv |-> local_peer_addr,
                addr_trans |-> remote_peer_addr,
                start_height |-> Ops!GetPeerFromNetwork(remote_peer_addr).chain_tip.height]
        ];
    return;
end procedure;

procedure version()
begin
    HandleVersionMessage:
        local_peer_addr := channels[self].payload.addr_recv;
        remote_peer_addr := channels[self].payload.addr_trans;
    SendVerackMessage:
        channels[self] := [
            header |-> [command_name |-> "verack"],
            payload |-> defaultInitValue
        ];
    return;
end procedure;

procedure verack()
begin
    HandleVerackMessage:
        await local_peer_addr # defaultInitValue /\ remote_peer_addr # defaultInitValue;
        the_network := Ops!UpdatePeerSet(local_peer_addr, remote_peer_addr);
    return;
end procedure;

procedure getblocks()
variables found_blocks, hash_provided, height_to_start;
begin
    HandleGetBlocksMessage:
        if channels[self].payload.hash_count = 0 then
            \* TODO: This is dirty but correct in some sense, it will build inventory with the 
            \* first `MaxGetBlocksInvResponse` blocks.
            found_blocks := Ops!FindBlocks(selected_remote_peer.blocks, 1, 1 + (MaxGetBlocksInvResponse - 1));
        else
            hash_provided := channels[self].payload.block_header_hashes;
            height_to_start := Ops!FindBlockByHash(selected_remote_peer.blocks, hash_provided).height + 1;
            found_blocks := Ops!FindBlocks(selected_remote_peer.blocks, height_to_start, height_to_start + (MaxGetBlocksInvResponse - 1));
        end if;
    SendInvMessage:
        channels[self] := [
            header |-> [command_name |-> "inv"],
            payload |-> [
                count |-> Cardinality({ r \in DOMAIN found_blocks : found_blocks[r] = TRUE }),
                inventory |-> [
                    h \in 1..Cardinality({ r \in DOMAIN found_blocks : found_blocks[r] = TRUE }) |-> [
                        type_identifier |-> "MSG_BLOCK",
                        hash |-> SetToSeq({ s.hash : s \in { r \in DOMAIN found_blocks : found_blocks[r] = TRUE } })[h]
                    ]
                ]
            ]
        ];
    return;
end procedure;

\* Request blocks from the selected remote peer by sending a getblocks message.
procedure request_blocks(hashes, id)
begin
    GetBlocksMessage:
        channels[id] := [
            header |-> [command_name |-> "getblocks"],
            payload |-> [
                \* TODO: Here we should send the last hash the local peer has.
                hash_count |-> Len(hashes),
                block_header_hashes |-> hashes,
                stop_hash |-> "0"]
        ];
    return;
end procedure;

\* Build getdata messages with the inventory received.
procedure inv()
begin
    SendGetDataMessage:
        \* Validate the inventory? For now we just pass it as it came so we just change the global message header.
        channels[self].header := [command_name |-> "getdata"];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure getdata()
variables c = 1, block_data, current_item;
begin
    \* Here we are sure the selected peer has the requested blocks.
    IncorporateLoop:
        while Len(channels[self].payload.inventory) > 0 do
            current_item := Head(channels[self].payload.inventory);
            block_data := Ops!FindBlockByHash(selected_remote_peer.blocks, current_item.hash);
            assert block_data.hash = current_item.hash;
                            
            the_network := Ops!UpdatePeerBlocks(the_network[self].peer, [
                height |-> block_data.height,
                hash |-> block_data.hash,
                block |-> block_data.block
            ]);

            channels[self].payload.inventory := Tail(channels[self].payload.inventory);
        end while;
    UpdateTip:
        the_network[self].chain_tip := [
            height |-> block_data.height,
            hash |-> block_data.hash
        ];
    return;
end procedure;

\* Peer Client Task
process client_task \in 1..MAX_PEERS
variables remote_peer_addr, local_peer_addr, id = self, hash_provided, height_to_start, command;
begin
    Listening:
        assert Len(the_network) >= id;
        assert Len(channels) >= id;
        if channels[id].header = defaultInitValue then
            goto Listening;
        end if;
    Requests:
        command := channels[id].header.command_name;
        if command = "version" then
            call version();
            goto Listening;
        elsif command = "verack" then
            call verack();
        elsif command = "getblocks" then
            call getblocks(); 
            goto Listening;
        elsif command = "inv" then
            call inv();
            goto Listening;
        elsif command = "getdata" then
            call getdata();
        end if;
    ClientTaskLoop:
        channels[id] := [header |-> defaultInitValue, payload |-> defaultInitValue];
        goto Listening;
end process;

process Peer \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS)
variables remote_peer_addr, id = self - DIFF_ID, remote_peer_height, ignore;
begin
    Connect:
        local_peer_addr := the_network[id].peer;
        remote_peer_addr := "peer1";
        remote_peer_height := the_network[1].chain_tip.height;
    
        \* don't do it for the seeder peer.
        await self > (DIFF_ID + 1);

        call create_connection(remote_peer_addr, local_peer_addr, id);
    SelectPeerForRequestFromLocalPeer:
        \*  Check connection is established.
        await Cardinality(the_network[id].peer_set) > 0;
        \* Get a peer from the local peer set.
        selected_remote_peer := Ops!GetPeerFromNetwork(
            CHOOSE peer_set \in Ops!GetPeerFromNetwork(local_peer_addr).peer_set : TRUE
        );
    RequestInventory:
        await selected_remote_peer.chain_tip.height > the_network[id].chain_tip.height;
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
\* BEGIN TRANSLATION (chksum(pcal) = "f7b16ec" /\ chksum(tla) = "de951036")
\* Process variable remote_peer_addr of process client_task at line 139 col 11 changed to remote_peer_addr_
\* Process variable local_peer_addr of process client_task at line 139 col 29 changed to local_peer_addr_
\* Process variable id of process client_task at line 139 col 46 changed to id_
\* Process variable hash_provided of process client_task at line 139 col 57 changed to hash_provided_
\* Process variable height_to_start of process client_task at line 139 col 72 changed to height_to_start_
\* Process variable remote_peer_addr of process Peer at line 169 col 11 changed to remote_peer_addr_P
\* Process variable id of process Peer at line 169 col 29 changed to id_P
\* Parameter local_peer_addr of procedure create_connection at line 23 col 47 changed to local_peer_addr_c
\* Parameter id of procedure create_connection at line 23 col 64 changed to id_c
CONSTANT defaultInitValue
VARIABLES the_network, selected_remote_peer, channels, pc, stack

(* define statement *)
LOCAL Ops == INSTANCE Operators

VARIABLES remote_peer_addr, local_peer_addr_c, id_c, found_blocks, 
          hash_provided, height_to_start, hashes, id, local_peer_addr, c, 
          block_data, current_item, remote_peer_addr_, local_peer_addr_, id_, 
          hash_provided_, height_to_start_, command, remote_peer_addr_P, id_P, 
          remote_peer_height, ignore

vars == << the_network, selected_remote_peer, channels, pc, stack, 
           remote_peer_addr, local_peer_addr_c, id_c, found_blocks, 
           hash_provided, height_to_start, hashes, id, local_peer_addr, c, 
           block_data, current_item, remote_peer_addr_, local_peer_addr_, id_, 
           hash_provided_, height_to_start_, command, remote_peer_addr_P, 
           id_P, remote_peer_height, ignore >>

ProcSet == (1..MAX_PEERS) \cup ((DIFF_ID + 1)..(DIFF_ID + MAX_PEERS))

Init == (* Global variables *)
        /\ the_network = SubSeq(Reverse(SetToSeq(PEERS)), 1, MAX_PEERS)
        /\ selected_remote_peer = defaultInitValue
        /\ channels = [i \in 1..MAX_PEERS |-> [header |-> defaultInitValue, payload |-> defaultInitValue]]
        (* Procedure create_connection *)
        /\ remote_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ local_peer_addr_c = [ self \in ProcSet |-> defaultInitValue]
        /\ id_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getblocks *)
        /\ found_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ hash_provided = [ self \in ProcSet |-> defaultInitValue]
        /\ height_to_start = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getdata *)
        /\ local_peer_addr = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> 1]
        /\ block_data = [ self \in ProcSet |-> defaultInitValue]
        /\ current_item = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_task *)
        /\ remote_peer_addr_ = [self \in 1..MAX_PEERS |-> defaultInitValue]
        /\ local_peer_addr_ = [self \in 1..MAX_PEERS |-> defaultInitValue]
        /\ id_ = [self \in 1..MAX_PEERS |-> self]
        /\ hash_provided_ = [self \in 1..MAX_PEERS |-> defaultInitValue]
        /\ height_to_start_ = [self \in 1..MAX_PEERS |-> defaultInitValue]
        /\ command = [self \in 1..MAX_PEERS |-> defaultInitValue]
        (* Process Peer *)
        /\ remote_peer_addr_P = [self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) |-> defaultInitValue]
        /\ id_P = [self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) |-> self - DIFF_ID]
        /\ remote_peer_height = [self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) |-> defaultInitValue]
        /\ ignore = [self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..MAX_PEERS -> "Listening"
                                        [] self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) -> "Connect"]

VersionMessage(self) == /\ pc[self] = "VersionMessage"
                        /\ channels' = [channels EXCEPT ![id_c[self]] =                 [
                                                                            header |-> [command_name |-> "version"],
                                                                            payload |-> [
                                                                                addr_recv |-> local_peer_addr_c[self],
                                                                                addr_trans |-> remote_peer_addr[self],
                                                                                start_height |-> Ops!GetPeerFromNetwork(remote_peer_addr[self]).chain_tip.height]
                                                                        ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = Head(stack[self]).remote_peer_addr]
                        /\ local_peer_addr_c' = [local_peer_addr_c EXCEPT ![self] = Head(stack[self]).local_peer_addr_c]
                        /\ id_c' = [id_c EXCEPT ![self] = Head(stack[self]).id_c]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        found_blocks, hash_provided, 
                                        height_to_start, hashes, id, 
                                        local_peer_addr, c, block_data, 
                                        current_item, remote_peer_addr_, 
                                        local_peer_addr_, id_, hash_provided_, 
                                        height_to_start_, command, 
                                        remote_peer_addr_P, id_P, 
                                        remote_peer_height, ignore >>

create_connection(self) == VersionMessage(self)

HandleVersionMessage(self) == /\ pc[self] = "HandleVersionMessage"
                              /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = channels[self].payload.addr_recv]
                              /\ remote_peer_addr' = [remote_peer_addr EXCEPT ![self] = channels[self].payload.addr_trans]
                              /\ pc' = [pc EXCEPT ![self] = "SendVerackMessage"]
                              /\ UNCHANGED << the_network, 
                                              selected_remote_peer, channels, 
                                              stack, local_peer_addr_c, id_c, 
                                              found_blocks, hash_provided, 
                                              height_to_start, hashes, id, c, 
                                              block_data, current_item, 
                                              remote_peer_addr_, 
                                              local_peer_addr_, id_, 
                                              hash_provided_, height_to_start_, 
                                              command, remote_peer_addr_P, 
                                              id_P, remote_peer_height, ignore >>

SendVerackMessage(self) == /\ pc[self] = "SendVerackMessage"
                           /\ channels' = [channels EXCEPT ![self] =                   [
                                                                         header |-> [command_name |-> "verack"],
                                                                         payload |-> defaultInitValue
                                                                     ]]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << the_network, selected_remote_peer, 
                                           remote_peer_addr, local_peer_addr_c, 
                                           id_c, found_blocks, hash_provided, 
                                           height_to_start, hashes, id, 
                                           local_peer_addr, c, block_data, 
                                           current_item, remote_peer_addr_, 
                                           local_peer_addr_, id_, 
                                           hash_provided_, height_to_start_, 
                                           command, remote_peer_addr_P, id_P, 
                                           remote_peer_height, ignore >>

version(self) == HandleVersionMessage(self) \/ SendVerackMessage(self)

HandleVerackMessage(self) == /\ pc[self] = "HandleVerackMessage"
                             /\ local_peer_addr[self] # defaultInitValue /\ remote_peer_addr[self] # defaultInitValue
                             /\ the_network' = Ops!UpdatePeerSet(local_peer_addr[self], remote_peer_addr[self])
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << selected_remote_peer, channels, 
                                             remote_peer_addr, 
                                             local_peer_addr_c, id_c, 
                                             found_blocks, hash_provided, 
                                             height_to_start, hashes, id, 
                                             local_peer_addr, c, block_data, 
                                             current_item, remote_peer_addr_, 
                                             local_peer_addr_, id_, 
                                             hash_provided_, height_to_start_, 
                                             command, remote_peer_addr_P, id_P, 
                                             remote_peer_height, ignore >>

verack(self) == HandleVerackMessage(self)

HandleGetBlocksMessage(self) == /\ pc[self] = "HandleGetBlocksMessage"
                                /\ IF channels[self].payload.hash_count = 0
                                      THEN /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(selected_remote_peer.blocks, 1, 1 + (MaxGetBlocksInvResponse - 1))]
                                           /\ UNCHANGED << hash_provided, 
                                                           height_to_start >>
                                      ELSE /\ hash_provided' = [hash_provided EXCEPT ![self] = channels[self].payload.block_header_hashes]
                                           /\ height_to_start' = [height_to_start EXCEPT ![self] = Ops!FindBlockByHash(selected_remote_peer.blocks, hash_provided'[self]).height + 1]
                                           /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(selected_remote_peer.blocks, height_to_start'[self], height_to_start'[self] + (MaxGetBlocksInvResponse - 1))]
                                /\ pc' = [pc EXCEPT ![self] = "SendInvMessage"]
                                /\ UNCHANGED << the_network, 
                                                selected_remote_peer, channels, 
                                                stack, remote_peer_addr, 
                                                local_peer_addr_c, id_c, 
                                                hashes, id, local_peer_addr, c, 
                                                block_data, current_item, 
                                                remote_peer_addr_, 
                                                local_peer_addr_, id_, 
                                                hash_provided_, 
                                                height_to_start_, command, 
                                                remote_peer_addr_P, id_P, 
                                                remote_peer_height, ignore >>

SendInvMessage(self) == /\ pc[self] = "SendInvMessage"
                        /\ channels' = [channels EXCEPT ![self] =                   [
                                                                      header |-> [command_name |-> "inv"],
                                                                      payload |-> [
                                                                          count |-> Cardinality({ r \in DOMAIN found_blocks[self] : found_blocks[self][r] = TRUE }),
                                                                          inventory |-> [
                                                                              h \in 1..Cardinality({ r \in DOMAIN found_blocks[self] : found_blocks[self][r] = TRUE }) |-> [
                                                                                  type_identifier |-> "MSG_BLOCK",
                                                                                  hash |-> SetToSeq({ s.hash : s \in { r \in DOMAIN found_blocks[self] : found_blocks[self][r] = TRUE } })[h]
                                                                              ]
                                                                          ]
                                                                      ]
                                                                  ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ found_blocks' = [found_blocks EXCEPT ![self] = Head(stack[self]).found_blocks]
                        /\ hash_provided' = [hash_provided EXCEPT ![self] = Head(stack[self]).hash_provided]
                        /\ height_to_start' = [height_to_start EXCEPT ![self] = Head(stack[self]).height_to_start]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        remote_peer_addr, local_peer_addr_c, 
                                        id_c, hashes, id, local_peer_addr, c, 
                                        block_data, current_item, 
                                        remote_peer_addr_, local_peer_addr_, 
                                        id_, hash_provided_, height_to_start_, 
                                        command, remote_peer_addr_P, id_P, 
                                        remote_peer_height, ignore >>

getblocks(self) == HandleGetBlocksMessage(self) \/ SendInvMessage(self)

GetBlocksMessage(self) == /\ pc[self] = "GetBlocksMessage"
                          /\ channels' = [channels EXCEPT ![id[self]] =                 [
                                                                            header |-> [command_name |-> "getblocks"],
                                                                            payload |-> [
                                                                        
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
                                          id_c, found_blocks, hash_provided, 
                                          height_to_start, local_peer_addr, c, 
                                          block_data, current_item, 
                                          remote_peer_addr_, local_peer_addr_, 
                                          id_, hash_provided_, 
                                          height_to_start_, command, 
                                          remote_peer_addr_P, id_P, 
                                          remote_peer_height, ignore >>

request_blocks(self) == GetBlocksMessage(self)

SendGetDataMessage(self) == /\ pc[self] = "SendGetDataMessage"
                            /\ channels' = [channels EXCEPT ![self].header = [command_name |-> "getdata"]]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << the_network, selected_remote_peer, 
                                            remote_peer_addr, 
                                            local_peer_addr_c, id_c, 
                                            found_blocks, hash_provided, 
                                            height_to_start, hashes, id, 
                                            local_peer_addr, c, block_data, 
                                            current_item, remote_peer_addr_, 
                                            local_peer_addr_, id_, 
                                            hash_provided_, height_to_start_, 
                                            command, remote_peer_addr_P, id_P, 
                                            remote_peer_height, ignore >>

inv(self) == SendGetDataMessage(self)

IncorporateLoop(self) == /\ pc[self] = "IncorporateLoop"
                         /\ IF Len(channels[self].payload.inventory) > 0
                               THEN /\ current_item' = [current_item EXCEPT ![self] = Head(channels[self].payload.inventory)]
                                    /\ block_data' = [block_data EXCEPT ![self] = Ops!FindBlockByHash(selected_remote_peer.blocks, current_item'[self].hash)]
                                    /\ Assert(block_data'[self].hash = current_item'[self].hash, 
                                              "Failure of assertion at line 119, column 13.")
                                    /\ the_network' =                Ops!UpdatePeerBlocks(local_peer_addr[self], [
                                                          height |-> block_data'[self].height,
                                                          hash |-> block_data'[self].hash,
                                                          block |-> block_data'[self].block
                                                      ])
                                    /\ channels' = [channels EXCEPT ![self].payload.inventory = Tail(channels[self].payload.inventory)]
                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateTip"]
                                    /\ UNCHANGED << the_network, channels, 
                                                    block_data, current_item >>
                         /\ UNCHANGED << selected_remote_peer, stack, 
                                         remote_peer_addr, local_peer_addr_c, 
                                         id_c, found_blocks, hash_provided, 
                                         height_to_start, hashes, id, 
                                         local_peer_addr, c, remote_peer_addr_, 
                                         local_peer_addr_, id_, hash_provided_, 
                                         height_to_start_, command, 
                                         remote_peer_addr_P, id_P, 
                                         remote_peer_height, ignore >>

UpdateTip(self) == /\ pc[self] = "UpdateTip"
                   /\ the_network' = [the_network EXCEPT ![self].chain_tip =                                [
                                                                                 height |-> block_data[self].height,
                                                                                 hash |-> block_data[self].hash
                                                                             ]]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                   /\ block_data' = [block_data EXCEPT ![self] = Head(stack[self]).block_data]
                   /\ current_item' = [current_item EXCEPT ![self] = Head(stack[self]).current_item]
                   /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = Head(stack[self]).local_peer_addr]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << selected_remote_peer, channels, 
                                   remote_peer_addr, local_peer_addr_c, id_c, 
                                   found_blocks, hash_provided, 
                                   height_to_start, hashes, id, 
                                   remote_peer_addr_, local_peer_addr_, id_, 
                                   hash_provided_, height_to_start_, command, 
                                   remote_peer_addr_P, id_P, 
                                   remote_peer_height, ignore >>

getdata(self) == IncorporateLoop(self) \/ UpdateTip(self)

Listening(self) == /\ pc[self] = "Listening"
                   /\ Assert(Len(the_network) >= id_[self], 
                             "Failure of assertion at line 142, column 9.")
                   /\ Assert(Len(channels) >= id_[self], 
                             "Failure of assertion at line 143, column 9.")
                   /\ IF channels[id_[self]].header = defaultInitValue
                         THEN /\ pc' = [pc EXCEPT ![self] = "Listening"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Requests"]
                   /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                                   stack, remote_peer_addr, local_peer_addr_c, 
                                   id_c, found_blocks, hash_provided, 
                                   height_to_start, hashes, id, 
                                   local_peer_addr, c, block_data, 
                                   current_item, remote_peer_addr_, 
                                   local_peer_addr_, id_, hash_provided_, 
                                   height_to_start_, command, 
                                   remote_peer_addr_P, id_P, 
                                   remote_peer_height, ignore >>

Requests(self) == /\ pc[self] = "Requests"
                  /\ command' = [command EXCEPT ![self] = channels[id_[self]].header.command_name]
                  /\ IF command'[self] = "version"
                        THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "version",
                                                                      pc        |->  "Listening" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "HandleVersionMessage"]
                             /\ UNCHANGED << found_blocks, hash_provided, 
                                             height_to_start, local_peer_addr, 
                                             c, block_data, current_item >>
                        ELSE /\ IF command'[self] = "verack"
                                   THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "verack",
                                                                                 pc        |->  "ClientTaskLoop" ] >>
                                                                             \o stack[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "HandleVerackMessage"]
                                        /\ UNCHANGED << found_blocks, 
                                                        hash_provided, 
                                                        height_to_start, 
                                                        local_peer_addr, c, 
                                                        block_data, 
                                                        current_item >>
                                   ELSE /\ IF command'[self] = "getblocks"
                                              THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getblocks",
                                                                                            pc        |->  "Listening",
                                                                                            found_blocks |->  found_blocks[self],
                                                                                            hash_provided |->  hash_provided[self],
                                                                                            height_to_start |->  height_to_start[self] ] >>
                                                                                        \o stack[self]]
                                                   /\ found_blocks' = [found_blocks EXCEPT ![self] = defaultInitValue]
                                                   /\ hash_provided' = [hash_provided EXCEPT ![self] = defaultInitValue]
                                                   /\ height_to_start' = [height_to_start EXCEPT ![self] = defaultInitValue]
                                                   /\ pc' = [pc EXCEPT ![self] = "HandleGetBlocksMessage"]
                                                   /\ UNCHANGED << local_peer_addr, 
                                                                   c, 
                                                                   block_data, 
                                                                   current_item >>
                                              ELSE /\ IF command'[self] = "inv"
                                                         THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "inv",
                                                                                                       pc        |->  "Listening" ] >>
                                                                                                   \o stack[self]]
                                                              /\ pc' = [pc EXCEPT ![self] = "SendGetDataMessage"]
                                                              /\ UNCHANGED << local_peer_addr, 
                                                                              c, 
                                                                              block_data, 
                                                                              current_item >>
                                                         ELSE /\ IF command'[self] = "getdata"
                                                                    THEN /\ /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = local_peer_addr_[self]]
                                                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getdata",
                                                                                                                     pc        |->  "ClientTaskLoop",
                                                                                                                     c         |->  c[self],
                                                                                                                     block_data |->  block_data[self],
                                                                                                                     current_item |->  current_item[self],
                                                                                                                     local_peer_addr |->  local_peer_addr[self] ] >>
                                                                                                                 \o stack[self]]
                                                                         /\ c' = [c EXCEPT ![self] = 1]
                                                                         /\ block_data' = [block_data EXCEPT ![self] = defaultInitValue]
                                                                         /\ current_item' = [current_item EXCEPT ![self] = defaultInitValue]
                                                                         /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "ClientTaskLoop"]
                                                                         /\ UNCHANGED << stack, 
                                                                                         local_peer_addr, 
                                                                                         c, 
                                                                                         block_data, 
                                                                                         current_item >>
                                                   /\ UNCHANGED << found_blocks, 
                                                                   hash_provided, 
                                                                   height_to_start >>
                  /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                                  remote_peer_addr, local_peer_addr_c, id_c, 
                                  hashes, id, remote_peer_addr_, 
                                  local_peer_addr_, id_, hash_provided_, 
                                  height_to_start_, remote_peer_addr_P, id_P, 
                                  remote_peer_height, ignore >>

ClientTaskLoop(self) == /\ pc[self] = "ClientTaskLoop"
                        /\ channels' = [channels EXCEPT ![id_[self]] = [header |-> defaultInitValue, payload |-> defaultInitValue]]
                        /\ pc' = [pc EXCEPT ![self] = "Listening"]
                        /\ UNCHANGED << the_network, selected_remote_peer, 
                                        stack, remote_peer_addr, 
                                        local_peer_addr_c, id_c, found_blocks, 
                                        hash_provided, height_to_start, hashes, 
                                        id, local_peer_addr, c, block_data, 
                                        current_item, remote_peer_addr_, 
                                        local_peer_addr_, id_, hash_provided_, 
                                        height_to_start_, command, 
                                        remote_peer_addr_P, id_P, 
                                        remote_peer_height, ignore >>

client_task(self) == Listening(self) \/ Requests(self)
                        \/ ClientTaskLoop(self)

Connect(self) == /\ pc[self] = "Connect"
                 /\ local_peer_addr' = [local_peer_addr EXCEPT ![self] = the_network[id_P[self]].peer]
                 /\ remote_peer_addr_P' = [remote_peer_addr_P EXCEPT ![self] = "peer1"]
                 /\ remote_peer_height' = [remote_peer_height EXCEPT ![self] = the_network[1].chain_tip.height]
                 /\ self > (DIFF_ID + 1)
                 /\ /\ id_c' = [id_c EXCEPT ![self] = id_P[self]]
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
                                 found_blocks, hash_provided, height_to_start, 
                                 hashes, id, c, block_data, current_item, 
                                 remote_peer_addr_, local_peer_addr_, id_, 
                                 hash_provided_, height_to_start_, command, 
                                 id_P, ignore >>

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
                                                           id_c, found_blocks, 
                                                           hash_provided, 
                                                           height_to_start, 
                                                           hashes, id, 
                                                           local_peer_addr, c, 
                                                           block_data, 
                                                           current_item, 
                                                           remote_peer_addr_, 
                                                           local_peer_addr_, 
                                                           id_, hash_provided_, 
                                                           height_to_start_, 
                                                           command, 
                                                           remote_peer_addr_P, 
                                                           id_P, 
                                                           remote_peer_height, 
                                                           ignore >>

RequestInventory(self) == /\ pc[self] = "RequestInventory"
                          /\ selected_remote_peer.chain_tip.height > the_network[id_P[self]].chain_tip.height
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << the_network, selected_remote_peer, 
                                          channels, stack, remote_peer_addr, 
                                          local_peer_addr_c, id_c, 
                                          found_blocks, hash_provided, 
                                          height_to_start, hashes, id, 
                                          local_peer_addr, c, block_data, 
                                          current_item, remote_peer_addr_, 
                                          local_peer_addr_, id_, 
                                          hash_provided_, height_to_start_, 
                                          command, remote_peer_addr_P, id_P, 
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
                              found_blocks, hash_provided, height_to_start, 
                              local_peer_addr, c, block_data, current_item, 
                              remote_peer_addr_, local_peer_addr_, id_, 
                              hash_provided_, height_to_start_, command, 
                              remote_peer_addr_P, id_P, remote_peer_height, 
                              ignore >>

CheckSync(self) == /\ pc[self] = "CheckSync"
                   /\ selected_remote_peer.chain_tip.height = the_network[id_P[self]].chain_tip.height
                   /\ PrintT("Network in sync!")
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << the_network, selected_remote_peer, channels, 
                                   stack, remote_peer_addr, local_peer_addr_c, 
                                   id_c, found_blocks, hash_provided, 
                                   height_to_start, hashes, id, 
                                   local_peer_addr, c, block_data, 
                                   current_item, remote_peer_addr_, 
                                   local_peer_addr_, id_, hash_provided_, 
                                   height_to_start_, command, 
                                   remote_peer_addr_P, id_P, 
                                   remote_peer_height, ignore >>

Peer(self) == Connect(self) \/ SelectPeerForRequestFromLocalPeer(self)
                 \/ RequestInventory(self) \/ Sync(self) \/ CheckSync(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ create_connection(self) \/ version(self)
                               \/ verack(self) \/ getblocks(self)
                               \/ request_blocks(self) \/ inv(self)
                               \/ getdata(self))
           \/ (\E self \in 1..MAX_PEERS: client_task(self))
           \/ (\E self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS): Peer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
