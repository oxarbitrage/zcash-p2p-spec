---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils, Blockchain

MaxGetBlocksInvResponse == 3

MAX_PEERS == 2

DIFF_ID == 1000

(*--algorithm p2p

variables
    the_network = SubSeq(Reverse(SetToSeq(PEERS)), 1, MAX_PEERS);

    channels = [i \in 1..MAX_PEERS |-> [header |-> defaultInitValue, payload |-> defaultInitValue]]
define
    LOCAL Ops == INSTANCE Operators
end define;

\* ...
procedure announce(id)
begin
    SendAddrMessage:
        channels[id] := [
            header |-> [command_name |-> "addr"],
            payload |-> [
                address_count |-> 1,
                addresses |-> the_network[id].peer
            ]
        ];
    return;
end procedure;

\* Create a connection between the remote and local peer.
procedure addr()
begin
    SendVersionMessage:
        channels[self] := [
            header |-> [command_name |-> "version"],
            payload |-> [
                addr_recv |-> the_network[self].peer,
                addr_trans |-> the_network[self].peer_set[1].address,
                \* We are allowed to do this because this message is sent from the remote_peer.
                start_height |-> Ops!GetPeerFromNetwork(the_network[self].peer_set[1].address).chain_tip.height]
        ];
    return;
end procedure;

procedure version()
begin
    HandleVersionMessage:
        the_network[self].peer_set[1].tip := channels[self].payload.start_height;
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
        \* Mark the connection as established.
        the_network[self].peer_set[1].established := TRUE;
    return;
end procedure;

procedure getblocks()
variables remote_peer_blocks, found_blocks, hash_provided, height_to_start;
begin
    HandleGetBlocksMessage:
        await Len(the_network[self].peer_set) > 0;
        \* The remote peer is the one creating this message so it is legal to access its blocks. 
        remote_peer_blocks := Ops!GetPeerFromNetwork(the_network[self].peer_set[1].address).blocks;

        if channels[self].payload.hash_count = 0 then
            \* TODO: This is dirty but correct in some sense, it will build inventory with the 
            \* first `MaxGetBlocksInvResponse` blocks.
            found_blocks := Ops!FindBlocks(remote_peer_blocks, 1, 1 + (MaxGetBlocksInvResponse - 1));
        else
            hash_provided := channels[self].payload.block_header_hashes;
            height_to_start := Ops!FindBlockByHash(remote_peer_blocks, hash_provided).height + 1;
            found_blocks := Ops!FindBlocks(remote_peer_blocks, height_to_start, height_to_start + (MaxGetBlocksInvResponse - 1));
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
    SendGetBlocksMessage:
        channels[id] := [
            header |-> [command_name |-> "getblocks"],
            payload |-> [
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
        \* TODO: Validate the inventory? For now we just pass the payload to `getdata`.
        channels[self].header := [command_name |-> "getdata"];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure getdata()
variables block_data, current_item;
begin
    IncorporateLoop:
        while Len(channels[self].payload.inventory) > 0 do
            current_item := Head(channels[self].payload.inventory);
            block_data := Ops!FindBlockByHash(
                Ops!GetPeerFromNetwork(the_network[self].peer_set[1].address).blocks,
                current_item.hash
            );
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
variables command;
begin
    Listening:
        assert Len(the_network) >= self /\ Len(channels) >= self;
        if channels[self].header = defaultInitValue then
            goto Listening;
        end if;
    Requests:
        command := channels[self].header.command_name;
        if command = "addr" then
            call addr();
            goto Listening;
        elsif command = "version" then
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
        channels[self] := [header |-> defaultInitValue, payload |-> defaultInitValue];
        goto Listening;
end process;

process Peer \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS)
variables id = self - DIFF_ID;
begin
    Announce:
        \* Only one peer in the peer set is currently supported.
        await Len(the_network[id].peer_set) = 1;
    
        call announce(id);
    CheckConnectionEstablished:
        await Len(the_network[id].peer_set) > 0 
            /\ the_network[id].peer_set[1].established = TRUE;
    RequestInventory:
        await the_network[id].peer_set[1].tip # defaultInitValue 
            /\ the_network[id].peer_set[1].tip > the_network[id].chain_tip.height;
        Sync:
            while the_network[id].chain_tip.height < the_network[id].peer_set[1].tip do
                await channels[id].header = defaultInitValue /\ channels[id].payload = defaultInitValue;
                if the_network[id].chain_tip.height = 0 then
                    call request_blocks(<<>>, id);
                else
                    call request_blocks(the_network[id].chain_tip.hash, id);
                end if;
            end while;
    CheckSync:
        await the_network[id].peer_set[1].tip = the_network[id].chain_tip.height;
        print "Network in sync!";
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "142a720f" /\ chksum(tla) = "f398785e")
\* Process variable id of process Peer at line 188 col 11 changed to id_
\* Parameter id of procedure announce at line 21 col 20 changed to id_a
CONSTANT defaultInitValue
VARIABLES the_network, channels, pc, stack

(* define statement *)
LOCAL Ops == INSTANCE Operators

VARIABLES id_a, remote_peer_blocks, found_blocks, hash_provided, 
          height_to_start, hashes, id, block_data, current_item, command, id_

vars == << the_network, channels, pc, stack, id_a, remote_peer_blocks, 
           found_blocks, hash_provided, height_to_start, hashes, id, 
           block_data, current_item, command, id_ >>

ProcSet == (1..MAX_PEERS) \cup ((DIFF_ID + 1)..(DIFF_ID + MAX_PEERS))

Init == (* Global variables *)
        /\ the_network = SubSeq(Reverse(SetToSeq(PEERS)), 1, MAX_PEERS)
        /\ channels = [i \in 1..MAX_PEERS |-> [header |-> defaultInitValue, payload |-> defaultInitValue]]
        (* Procedure announce *)
        /\ id_a = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getblocks *)
        /\ remote_peer_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ found_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ hash_provided = [ self \in ProcSet |-> defaultInitValue]
        /\ height_to_start = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getdata *)
        /\ block_data = [ self \in ProcSet |-> defaultInitValue]
        /\ current_item = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_task *)
        /\ command = [self \in 1..MAX_PEERS |-> defaultInitValue]
        (* Process Peer *)
        /\ id_ = [self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) |-> self - DIFF_ID]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..MAX_PEERS -> "Listening"
                                        [] self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS) -> "Announce"]

SendAddrMessage(self) == /\ pc[self] = "SendAddrMessage"
                         /\ channels' = [channels EXCEPT ![id_a[self]] =                 [
                                                                             header |-> [command_name |-> "addr"],
                                                                             payload |-> [
                                                                                 address_count |-> 1,
                                                                                 addresses |-> the_network[id_a[self]].peer
                                                                             ]
                                                                         ]]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ id_a' = [id_a EXCEPT ![self] = Head(stack[self]).id_a]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << the_network, remote_peer_blocks, 
                                         found_blocks, hash_provided, 
                                         height_to_start, hashes, id, 
                                         block_data, current_item, command, 
                                         id_ >>

announce(self) == SendAddrMessage(self)

SendVersionMessage(self) == /\ pc[self] = "SendVersionMessage"
                            /\ channels' = [channels EXCEPT ![self] =                   [
                                                                          header |-> [command_name |-> "version"],
                                                                          payload |-> [
                                                                              addr_recv |-> the_network[self].peer,
                                                                              addr_trans |-> the_network[self].peer_set[1].address,
                                                                      
                                                                              start_height |-> Ops!GetPeerFromNetwork(the_network[self].peer_set[1].address).chain_tip.height]
                                                                      ]]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << the_network, id_a, 
                                            remote_peer_blocks, found_blocks, 
                                            hash_provided, height_to_start, 
                                            hashes, id, block_data, 
                                            current_item, command, id_ >>

addr(self) == SendVersionMessage(self)

HandleVersionMessage(self) == /\ pc[self] = "HandleVersionMessage"
                              /\ the_network' = [the_network EXCEPT ![self].peer_set[1].tip = channels[self].payload.start_height]
                              /\ pc' = [pc EXCEPT ![self] = "SendVerackMessage"]
                              /\ UNCHANGED << channels, stack, id_a, 
                                              remote_peer_blocks, found_blocks, 
                                              hash_provided, height_to_start, 
                                              hashes, id, block_data, 
                                              current_item, command, id_ >>

SendVerackMessage(self) == /\ pc[self] = "SendVerackMessage"
                           /\ channels' = [channels EXCEPT ![self] =                   [
                                                                         header |-> [command_name |-> "verack"],
                                                                         payload |-> defaultInitValue
                                                                     ]]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << the_network, id_a, 
                                           remote_peer_blocks, found_blocks, 
                                           hash_provided, height_to_start, 
                                           hashes, id, block_data, 
                                           current_item, command, id_ >>

version(self) == HandleVersionMessage(self) \/ SendVerackMessage(self)

HandleVerackMessage(self) == /\ pc[self] = "HandleVerackMessage"
                             /\ the_network' = [the_network EXCEPT ![self].peer_set[1].established = TRUE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << channels, id_a, 
                                             remote_peer_blocks, found_blocks, 
                                             hash_provided, height_to_start, 
                                             hashes, id, block_data, 
                                             current_item, command, id_ >>

verack(self) == HandleVerackMessage(self)

HandleGetBlocksMessage(self) == /\ pc[self] = "HandleGetBlocksMessage"
                                /\ Len(the_network[self].peer_set) > 0
                                /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = Ops!GetPeerFromNetwork(the_network[self].peer_set[1].address).blocks]
                                /\ IF channels[self].payload.hash_count = 0
                                      THEN /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(remote_peer_blocks'[self], 1, 1 + (MaxGetBlocksInvResponse - 1))]
                                           /\ UNCHANGED << hash_provided, 
                                                           height_to_start >>
                                      ELSE /\ hash_provided' = [hash_provided EXCEPT ![self] = channels[self].payload.block_header_hashes]
                                           /\ height_to_start' = [height_to_start EXCEPT ![self] = Ops!FindBlockByHash(remote_peer_blocks'[self], hash_provided'[self]).height + 1]
                                           /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(remote_peer_blocks'[self], height_to_start'[self], height_to_start'[self] + (MaxGetBlocksInvResponse - 1))]
                                /\ pc' = [pc EXCEPT ![self] = "SendInvMessage"]
                                /\ UNCHANGED << the_network, channels, stack, 
                                                id_a, hashes, id, block_data, 
                                                current_item, command, id_ >>

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
                        /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = Head(stack[self]).remote_peer_blocks]
                        /\ found_blocks' = [found_blocks EXCEPT ![self] = Head(stack[self]).found_blocks]
                        /\ hash_provided' = [hash_provided EXCEPT ![self] = Head(stack[self]).hash_provided]
                        /\ height_to_start' = [height_to_start EXCEPT ![self] = Head(stack[self]).height_to_start]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, id_a, hashes, id, 
                                        block_data, current_item, command, id_ >>

getblocks(self) == HandleGetBlocksMessage(self) \/ SendInvMessage(self)

SendGetBlocksMessage(self) == /\ pc[self] = "SendGetBlocksMessage"
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
                              /\ UNCHANGED << the_network, id_a, 
                                              remote_peer_blocks, found_blocks, 
                                              hash_provided, height_to_start, 
                                              block_data, current_item, 
                                              command, id_ >>

request_blocks(self) == SendGetBlocksMessage(self)

SendGetDataMessage(self) == /\ pc[self] = "SendGetDataMessage"
                            /\ channels' = [channels EXCEPT ![self].header = [command_name |-> "getdata"]]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << the_network, id_a, 
                                            remote_peer_blocks, found_blocks, 
                                            hash_provided, height_to_start, 
                                            hashes, id, block_data, 
                                            current_item, command, id_ >>

inv(self) == SendGetDataMessage(self)

IncorporateLoop(self) == /\ pc[self] = "IncorporateLoop"
                         /\ IF Len(channels[self].payload.inventory) > 0
                               THEN /\ current_item' = [current_item EXCEPT ![self] = Head(channels[self].payload.inventory)]
                                    /\ block_data' = [block_data EXCEPT ![self] =               Ops!FindBlockByHash(
                                                                                      Ops!GetPeerFromNetwork(the_network[self].peer_set[1].address).blocks,
                                                                                      current_item'[self].hash
                                                                                  )]
                                    /\ Assert(block_data'[self].hash = current_item'[self].hash, 
                                              "Failure of assertion at line 136, column 13.")
                                    /\ the_network' =                Ops!UpdatePeerBlocks(the_network[self].peer, [
                                                          height |-> block_data'[self].height,
                                                          hash |-> block_data'[self].hash,
                                                          block |-> block_data'[self].block
                                                      ])
                                    /\ channels' = [channels EXCEPT ![self].payload.inventory = Tail(channels[self].payload.inventory)]
                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateTip"]
                                    /\ UNCHANGED << the_network, channels, 
                                                    block_data, current_item >>
                         /\ UNCHANGED << stack, id_a, remote_peer_blocks, 
                                         found_blocks, hash_provided, 
                                         height_to_start, hashes, id, command, 
                                         id_ >>

UpdateTip(self) == /\ pc[self] = "UpdateTip"
                   /\ the_network' = [the_network EXCEPT ![self].chain_tip =                                [
                                                                                 height |-> block_data[self].height,
                                                                                 hash |-> block_data[self].hash
                                                                             ]]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ block_data' = [block_data EXCEPT ![self] = Head(stack[self]).block_data]
                   /\ current_item' = [current_item EXCEPT ![self] = Head(stack[self]).current_item]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << channels, id_a, remote_peer_blocks, 
                                   found_blocks, hash_provided, 
                                   height_to_start, hashes, id, command, id_ >>

getdata(self) == IncorporateLoop(self) \/ UpdateTip(self)

Listening(self) == /\ pc[self] = "Listening"
                   /\ Assert(Len(the_network) >= self /\ Len(channels) >= self, 
                             "Failure of assertion at line 159, column 9.")
                   /\ IF channels[self].header = defaultInitValue
                         THEN /\ pc' = [pc EXCEPT ![self] = "Listening"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Requests"]
                   /\ UNCHANGED << the_network, channels, stack, id_a, 
                                   remote_peer_blocks, found_blocks, 
                                   hash_provided, height_to_start, hashes, id, 
                                   block_data, current_item, command, id_ >>

Requests(self) == /\ pc[self] = "Requests"
                  /\ command' = [command EXCEPT ![self] = channels[self].header.command_name]
                  /\ IF command'[self] = "addr"
                        THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addr",
                                                                      pc        |->  "Listening" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "SendVersionMessage"]
                             /\ UNCHANGED << remote_peer_blocks, found_blocks, 
                                             hash_provided, height_to_start, 
                                             block_data, current_item >>
                        ELSE /\ IF command'[self] = "version"
                                   THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "version",
                                                                                 pc        |->  "Listening" ] >>
                                                                             \o stack[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "HandleVersionMessage"]
                                        /\ UNCHANGED << remote_peer_blocks, 
                                                        found_blocks, 
                                                        hash_provided, 
                                                        height_to_start, 
                                                        block_data, 
                                                        current_item >>
                                   ELSE /\ IF command'[self] = "verack"
                                              THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "verack",
                                                                                            pc        |->  "ClientTaskLoop" ] >>
                                                                                        \o stack[self]]
                                                   /\ pc' = [pc EXCEPT ![self] = "HandleVerackMessage"]
                                                   /\ UNCHANGED << remote_peer_blocks, 
                                                                   found_blocks, 
                                                                   hash_provided, 
                                                                   height_to_start, 
                                                                   block_data, 
                                                                   current_item >>
                                              ELSE /\ IF command'[self] = "getblocks"
                                                         THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getblocks",
                                                                                                       pc        |->  "Listening",
                                                                                                       remote_peer_blocks |->  remote_peer_blocks[self],
                                                                                                       found_blocks |->  found_blocks[self],
                                                                                                       hash_provided |->  hash_provided[self],
                                                                                                       height_to_start |->  height_to_start[self] ] >>
                                                                                                   \o stack[self]]
                                                              /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = defaultInitValue]
                                                              /\ found_blocks' = [found_blocks EXCEPT ![self] = defaultInitValue]
                                                              /\ hash_provided' = [hash_provided EXCEPT ![self] = defaultInitValue]
                                                              /\ height_to_start' = [height_to_start EXCEPT ![self] = defaultInitValue]
                                                              /\ pc' = [pc EXCEPT ![self] = "HandleGetBlocksMessage"]
                                                              /\ UNCHANGED << block_data, 
                                                                              current_item >>
                                                         ELSE /\ IF command'[self] = "inv"
                                                                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "inv",
                                                                                                                  pc        |->  "Listening" ] >>
                                                                                                              \o stack[self]]
                                                                         /\ pc' = [pc EXCEPT ![self] = "SendGetDataMessage"]
                                                                         /\ UNCHANGED << block_data, 
                                                                                         current_item >>
                                                                    ELSE /\ IF command'[self] = "getdata"
                                                                               THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getdata",
                                                                                                                             pc        |->  "ClientTaskLoop",
                                                                                                                             block_data |->  block_data[self],
                                                                                                                             current_item |->  current_item[self] ] >>
                                                                                                                         \o stack[self]]
                                                                                    /\ block_data' = [block_data EXCEPT ![self] = defaultInitValue]
                                                                                    /\ current_item' = [current_item EXCEPT ![self] = defaultInitValue]
                                                                                    /\ pc' = [pc EXCEPT ![self] = "IncorporateLoop"]
                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ClientTaskLoop"]
                                                                                    /\ UNCHANGED << stack, 
                                                                                                    block_data, 
                                                                                                    current_item >>
                                                              /\ UNCHANGED << remote_peer_blocks, 
                                                                              found_blocks, 
                                                                              hash_provided, 
                                                                              height_to_start >>
                  /\ UNCHANGED << the_network, channels, id_a, hashes, id, id_ >>

ClientTaskLoop(self) == /\ pc[self] = "ClientTaskLoop"
                        /\ channels' = [channels EXCEPT ![self] = [header |-> defaultInitValue, payload |-> defaultInitValue]]
                        /\ pc' = [pc EXCEPT ![self] = "Listening"]
                        /\ UNCHANGED << the_network, stack, id_a, 
                                        remote_peer_blocks, found_blocks, 
                                        hash_provided, height_to_start, hashes, 
                                        id, block_data, current_item, command, 
                                        id_ >>

client_task(self) == Listening(self) \/ Requests(self)
                        \/ ClientTaskLoop(self)

Announce(self) == /\ pc[self] = "Announce"
                  /\ Len(the_network[id_[self]].peer_set) = 1
                  /\ /\ id_a' = [id_a EXCEPT ![self] = id_[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "announce",
                                                              pc        |->  "CheckConnectionEstablished",
                                                              id_a      |->  id_a[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "SendAddrMessage"]
                  /\ UNCHANGED << the_network, channels, remote_peer_blocks, 
                                  found_blocks, hash_provided, height_to_start, 
                                  hashes, id, block_data, current_item, 
                                  command, id_ >>

CheckConnectionEstablished(self) == /\ pc[self] = "CheckConnectionEstablished"
                                    /\   Len(the_network[id_[self]].peer_set) > 0
                                       /\ the_network[id_[self]].peer_set[1].established = TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "RequestInventory"]
                                    /\ UNCHANGED << the_network, channels, 
                                                    stack, id_a, 
                                                    remote_peer_blocks, 
                                                    found_blocks, 
                                                    hash_provided, 
                                                    height_to_start, hashes, 
                                                    id, block_data, 
                                                    current_item, command, id_ >>

RequestInventory(self) == /\ pc[self] = "RequestInventory"
                          /\   the_network[id_[self]].peer_set[1].tip # defaultInitValue
                             /\ the_network[id_[self]].peer_set[1].tip > the_network[id_[self]].chain_tip.height
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << the_network, channels, stack, id_a, 
                                          remote_peer_blocks, found_blocks, 
                                          hash_provided, height_to_start, 
                                          hashes, id, block_data, current_item, 
                                          command, id_ >>

Sync(self) == /\ pc[self] = "Sync"
              /\ IF the_network[id_[self]].chain_tip.height < the_network[id_[self]].peer_set[1].tip
                    THEN /\ channels[id_[self]].header = defaultInitValue /\ channels[id_[self]].payload = defaultInitValue
                         /\ IF the_network[id_[self]].chain_tip.height = 0
                               THEN /\ /\ hashes' = [hashes EXCEPT ![self] = <<>>]
                                       /\ id' = [id EXCEPT ![self] = id_[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                pc        |->  "Sync",
                                                                                hashes    |->  hashes[self],
                                                                                id        |->  id[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "SendGetBlocksMessage"]
                               ELSE /\ /\ hashes' = [hashes EXCEPT ![self] = the_network[id_[self]].chain_tip.hash]
                                       /\ id' = [id EXCEPT ![self] = id_[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                pc        |->  "Sync",
                                                                                hashes    |->  hashes[self],
                                                                                id        |->  id[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "SendGetBlocksMessage"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CheckSync"]
                         /\ UNCHANGED << stack, hashes, id >>
              /\ UNCHANGED << the_network, channels, id_a, remote_peer_blocks, 
                              found_blocks, hash_provided, height_to_start, 
                              block_data, current_item, command, id_ >>

CheckSync(self) == /\ pc[self] = "CheckSync"
                   /\ the_network[id_[self]].peer_set[1].tip = the_network[id_[self]].chain_tip.height
                   /\ PrintT("Network in sync!")
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << the_network, channels, stack, id_a, 
                                   remote_peer_blocks, found_blocks, 
                                   hash_provided, height_to_start, hashes, id, 
                                   block_data, current_item, command, id_ >>

Peer(self) == Announce(self) \/ CheckConnectionEstablished(self)
                 \/ RequestInventory(self) \/ Sync(self) \/ CheckSync(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ announce(self) \/ addr(self)
                               \/ version(self) \/ verack(self)
                               \/ getblocks(self) \/ request_blocks(self)
                               \/ inv(self) \/ getdata(self))
           \/ (\E self \in 1..MAX_PEERS: client_task(self))
           \/ (\E self \in (DIFF_ID + 1)..(DIFF_ID + MAX_PEERS): Peer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
