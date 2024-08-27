---- MODULE p2p ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils, Blockchain

\* The maximum number of blocks to be retrieved in a single getblocks response.
MaxGetBlocksInvResponse == 3

\* Difference in the process identifier so that it does not conflict with the existing task processes.
PeerProcessDiffId == 1000

(*--algorithm p2p

variables
    \* Represent the whole universe of peers in the network with all of their data.
    the_network = PEERS;

    \* Each peer has a channel to communicate with other peers.
    channels = [i \in 1..Len(PEERS) |-> [header |-> defaultInitValue, payload |-> defaultInitValue]]
define
    \* Import the operators used in the algorithm.
    LOCAL Ops == INSTANCE Operators
end define;

\* Announce the intention of a peer to connect with another in the network by sending an `addr` message.
procedure announce(id)
begin
    SendAddrMsg:
        channels[id] := [
            header |-> [command_name |-> "addr"],
            payload |-> [
                address_count |-> 1,
                addresses |-> the_network[id].peer
            ]
        ];
    return;
end procedure;

\* Given that an `addr` message is received, send a `version` message from the remote peer to start the connection.
procedure addr()
begin
    SendVersionMsg:
        channels[self] := [
            header |-> [command_name |-> "version"],
            payload |-> [
                addr_recv |-> the_network[self].peer,
                addr_trans |-> the_network[self].peer_set[1].address,
                start_height |-> Ops!GetPeerTip(the_network[self].peer_set[1].address)]
        ];
    return;
end procedure;

\* Given a `version` message is received, send `verack` to acknowledge the connection.
procedure version()
begin
    HandleVersionMsg:
        the_network[self].peer_set[1].tip := channels[self].payload.start_height;
    SendVerackMsg:
        channels[self] := [
            header |-> [command_name |-> "verack"],
            payload |-> defaultInitValue
        ];
    return;
end procedure;

\* Given a `verack` message is received, establish the connection.
procedure verack()
begin
    HandleVerackMsg:
        the_network[self].peer_set[1].established := TRUE;
    return;
end procedure;

\* Given a `getblocks` message is received, send an `inv` message with the blocks requested.
procedure getblocks()
variables found_blocks, hash_count, block_header_hashes, remote_peer_blocks, start_height, end_height;
begin
    HandleGetBlocksMsg:
        \* Retrieve necessary values from the channel payload
        hash_count := channels[self].payload.hash_count;
        block_header_hashes := channels[self].payload.block_header_hashes;

        \* Fetch the blocks of the remote peer
        remote_peer_blocks := Ops!GetPeerBlocks(the_network[self].peer_set[1].address);

        \* Determine the range of blocks to retrieve
        if hash_count = 0 then
            start_height := 1;
        else
            \* Assuming the hashes are in order, the height of the first hash should be the tip, ignore the rest. 
            start_height := Ops!FindBlockByHash(remote_peer_blocks, block_header_hashes[1]).height + 1;
        end if;
        end_height := start_height + (MaxGetBlocksInvResponse - 1);

        \* Find the blocks within the specified range.
        found_blocks := Ops!FindBlocks(remote_peer_blocks, start_height, end_height);
    SendInvMsg:
        channels[self] := [
            header |-> [command_name |-> "inv"],
            payload |-> [
                count |-> Cardinality(found_blocks),
                inventory |-> [
                    h \in 1..Cardinality(found_blocks) |-> [
                        type_identifier |-> "MSG_BLOCK",
                        hash |-> SetToSeq({ s.hash : s \in found_blocks })[h]
                    ]
                ]
            ]
        ];
    return;
end procedure;

\* Request blocks from the remote peer by sending a `getblocks` message with local hashes.
procedure request_blocks(hashes, id)
begin
    SendGetBlocksMsg:
        channels[id] := [
            header |-> [command_name |-> "getblocks"],
            payload |-> [
                hash_count |-> Len(hashes),
                block_header_hashes |-> hashes]
        ];
    return;
end procedure;

\* Given an `inv` message is received, send a `getdata` message to request the blocks.
procedure inv()
begin
    SendGetDataMsg:
        channels[self] := [
            header |-> [command_name |-> "getdata"],
            payload |-> channels[self].payload
        ];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure getdata()
variables blocks_data;
begin
    Incorporate:
        blocks_data := [item \in 1..Len(channels[self].payload.inventory) |->
            Ops!FindBlockByHash(
                Ops!GetPeerBlocks(the_network[self].peer_set[1].address), channels[self].payload.inventory[item].hash
            )
        ];
        the_network[self].blocks := the_network[self].blocks \cup ToSet(blocks_data);
    UpdateTip:
        the_network[self].chain_tip := [
            height |-> blocks_data[Len(blocks_data)].height,
            hash |-> blocks_data[Len(blocks_data)].hash
        ];
    return;
end procedure;

\* The main process of the peer to listen to incoming messages.
process LISTEN \in 1 .. Len(PEERS)
begin
    Listening:
        assert Len(the_network) >= self /\ Len(channels) >= self;
        if channels[self].header = defaultInitValue then
            goto Listening;
        end if;
    Requests:
        with command = channels[self].header.command_name do
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
        end with;
    ClientTaskLoop:
        channels[self] := [header |-> defaultInitValue, payload |-> defaultInitValue];
        goto Listening;
end process;

\* The process to synchronize the local peer with the remote peer.
process SYNC \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(PEERS)
variables id = self - PeerProcessDiffId;
begin
    Announce:
        \* Only one peer in the peer set is currently supported.
        await Len(the_network[id].peer_set) = 1;

        call announce(id);
    RequestInventory:
        \* Make sure the connection is established before requesting any block.
        await Len(the_network[id].peer_set) > 0 /\ the_network[id].peer_set[1].established = TRUE;
        Syncronizer:
            while the_network[id].chain_tip.height < the_network[id].peer_set[1].tip do
                \* Wait for the peer channel to be empty before requesting new blocks.
                await channels[id].header = defaultInitValue /\ channels[id].payload = defaultInitValue;
                \* Request blocks.
                if the_network[id].chain_tip.height = 0 then
                    call request_blocks(<<>>, id);
                else
                    call request_blocks(<<the_network[id].chain_tip.hash>>, id);
                end if;
            end while;
    CheckSync:
        \* Channels are empty, representing message exchange is done.
        await channels[id].header = defaultInitValue /\ channels[id].payload = defaultInitValue;
        \* Local tip is in sync with the remote peer tip.
        await the_network[id].peer_set[1].tip = the_network[id].chain_tip.height;
        print "Peer is in sync!";
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "65553bc0" /\ chksum(tla) = "acdd4fd9")
\* Process variable id of process SYNC at line 189 col 11 changed to id_
\* Parameter id of procedure announce at line 24 col 20 changed to id_a
CONSTANT defaultInitValue
VARIABLES the_network, channels, pc, stack

(* define statement *)
LOCAL Ops == INSTANCE Operators

VARIABLES id_a, found_blocks, hash_count, block_header_hashes, 
          remote_peer_blocks, start_height, end_height, hashes, id, 
          blocks_data, id_

vars == << the_network, channels, pc, stack, id_a, found_blocks, hash_count, 
           block_header_hashes, remote_peer_blocks, start_height, end_height, 
           hashes, id, blocks_data, id_ >>

ProcSet == (1 .. Len(PEERS)) \cup (PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(PEERS))

Init == (* Global variables *)
        /\ the_network = PEERS
        /\ channels = [i \in 1..Len(PEERS) |-> [header |-> defaultInitValue, payload |-> defaultInitValue]]
        (* Procedure announce *)
        /\ id_a = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getblocks *)
        /\ found_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ hash_count = [ self \in ProcSet |-> defaultInitValue]
        /\ block_header_hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ start_height = [ self \in ProcSet |-> defaultInitValue]
        /\ end_height = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getdata *)
        /\ blocks_data = [ self \in ProcSet |-> defaultInitValue]
        (* Process SYNC *)
        /\ id_ = [self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(PEERS) |-> self - PeerProcessDiffId]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1 .. Len(PEERS) -> "Listening"
                                        [] self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(PEERS) -> "Announce"]

SendAddrMsg(self) == /\ pc[self] = "SendAddrMsg"
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
                     /\ UNCHANGED << the_network, found_blocks, hash_count, 
                                     block_header_hashes, remote_peer_blocks, 
                                     start_height, end_height, hashes, id, 
                                     blocks_data, id_ >>

announce(self) == SendAddrMsg(self)

SendVersionMsg(self) == /\ pc[self] = "SendVersionMsg"
                        /\ channels' = [channels EXCEPT ![self] =                   [
                                                                      header |-> [command_name |-> "version"],
                                                                      payload |-> [
                                                                          addr_recv |-> the_network[self].peer,
                                                                          addr_trans |-> the_network[self].peer_set[1].address,
                                                                          start_height |-> Ops!GetPeerTip(the_network[self].peer_set[1].address)]
                                                                  ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, id_a, found_blocks, 
                                        hash_count, block_header_hashes, 
                                        remote_peer_blocks, start_height, 
                                        end_height, hashes, id, blocks_data, 
                                        id_ >>

addr(self) == SendVersionMsg(self)

HandleVersionMsg(self) == /\ pc[self] = "HandleVersionMsg"
                          /\ the_network' = [the_network EXCEPT ![self].peer_set[1].tip = channels[self].payload.start_height]
                          /\ pc' = [pc EXCEPT ![self] = "SendVerackMsg"]
                          /\ UNCHANGED << channels, stack, id_a, found_blocks, 
                                          hash_count, block_header_hashes, 
                                          remote_peer_blocks, start_height, 
                                          end_height, hashes, id, blocks_data, 
                                          id_ >>

SendVerackMsg(self) == /\ pc[self] = "SendVerackMsg"
                       /\ channels' = [channels EXCEPT ![self] =                   [
                                                                     header |-> [command_name |-> "verack"],
                                                                     payload |-> defaultInitValue
                                                                 ]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << the_network, id_a, found_blocks, 
                                       hash_count, block_header_hashes, 
                                       remote_peer_blocks, start_height, 
                                       end_height, hashes, id, blocks_data, 
                                       id_ >>

version(self) == HandleVersionMsg(self) \/ SendVerackMsg(self)

HandleVerackMsg(self) == /\ pc[self] = "HandleVerackMsg"
                         /\ the_network' = [the_network EXCEPT ![self].peer_set[1].established = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << channels, id_a, found_blocks, 
                                         hash_count, block_header_hashes, 
                                         remote_peer_blocks, start_height, 
                                         end_height, hashes, id, blocks_data, 
                                         id_ >>

verack(self) == HandleVerackMsg(self)

HandleGetBlocksMsg(self) == /\ pc[self] = "HandleGetBlocksMsg"
                            /\ hash_count' = [hash_count EXCEPT ![self] = channels[self].payload.hash_count]
                            /\ block_header_hashes' = [block_header_hashes EXCEPT ![self] = channels[self].payload.block_header_hashes]
                            /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = Ops!GetPeerBlocks(the_network[self].peer_set[1].address)]
                            /\ IF hash_count'[self] = 0
                                  THEN /\ start_height' = [start_height EXCEPT ![self] = 1]
                                  ELSE /\ start_height' = [start_height EXCEPT ![self] = Ops!FindBlockByHash(remote_peer_blocks'[self], block_header_hashes'[self][1]).height + 1]
                            /\ end_height' = [end_height EXCEPT ![self] = start_height'[self] + (MaxGetBlocksInvResponse - 1)]
                            /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(remote_peer_blocks'[self], start_height'[self], end_height'[self])]
                            /\ pc' = [pc EXCEPT ![self] = "SendInvMsg"]
                            /\ UNCHANGED << the_network, channels, stack, id_a, 
                                            hashes, id, blocks_data, id_ >>

SendInvMsg(self) == /\ pc[self] = "SendInvMsg"
                    /\ channels' = [channels EXCEPT ![self] =                   [
                                                                  header |-> [command_name |-> "inv"],
                                                                  payload |-> [
                                                                      count |-> Cardinality(found_blocks[self]),
                                                                      inventory |-> [
                                                                          h \in 1..Cardinality(found_blocks[self]) |-> [
                                                                              type_identifier |-> "MSG_BLOCK",
                                                                              hash |-> SetToSeq({ s.hash : s \in found_blocks[self] })[h]
                                                                          ]
                                                                      ]
                                                                  ]
                                                              ]]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ found_blocks' = [found_blocks EXCEPT ![self] = Head(stack[self]).found_blocks]
                    /\ hash_count' = [hash_count EXCEPT ![self] = Head(stack[self]).hash_count]
                    /\ block_header_hashes' = [block_header_hashes EXCEPT ![self] = Head(stack[self]).block_header_hashes]
                    /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = Head(stack[self]).remote_peer_blocks]
                    /\ start_height' = [start_height EXCEPT ![self] = Head(stack[self]).start_height]
                    /\ end_height' = [end_height EXCEPT ![self] = Head(stack[self]).end_height]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << the_network, id_a, hashes, id, blocks_data, 
                                    id_ >>

getblocks(self) == HandleGetBlocksMsg(self) \/ SendInvMsg(self)

SendGetBlocksMsg(self) == /\ pc[self] = "SendGetBlocksMsg"
                          /\ channels' = [channels EXCEPT ![id[self]] =                 [
                                                                            header |-> [command_name |-> "getblocks"],
                                                                            payload |-> [
                                                                                hash_count |-> Len(hashes[self]),
                                                                                block_header_hashes |-> hashes[self]]
                                                                        ]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ hashes' = [hashes EXCEPT ![self] = Head(stack[self]).hashes]
                          /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, id_a, found_blocks, 
                                          hash_count, block_header_hashes, 
                                          remote_peer_blocks, start_height, 
                                          end_height, blocks_data, id_ >>

request_blocks(self) == SendGetBlocksMsg(self)

SendGetDataMsg(self) == /\ pc[self] = "SendGetDataMsg"
                        /\ channels' = [channels EXCEPT ![self] =                   [
                                                                      header |-> [command_name |-> "getdata"],
                                                                      payload |-> channels[self].payload
                                                                  ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, id_a, found_blocks, 
                                        hash_count, block_header_hashes, 
                                        remote_peer_blocks, start_height, 
                                        end_height, hashes, id, blocks_data, 
                                        id_ >>

inv(self) == SendGetDataMsg(self)

Incorporate(self) == /\ pc[self] = "Incorporate"
                     /\ blocks_data' = [blocks_data EXCEPT ![self] =                [item \in 1..Len(channels[self].payload.inventory) |->
                                                                         Ops!FindBlockByHash(
                                                                             Ops!GetPeerBlocks(the_network[self].peer_set[1].address), channels[self].payload.inventory[item].hash
                                                                         )
                                                                     ]]
                     /\ the_network' = [the_network EXCEPT ![self].blocks = the_network[self].blocks \cup ToSet(blocks_data'[self])]
                     /\ pc' = [pc EXCEPT ![self] = "UpdateTip"]
                     /\ UNCHANGED << channels, stack, id_a, found_blocks, 
                                     hash_count, block_header_hashes, 
                                     remote_peer_blocks, start_height, 
                                     end_height, hashes, id, id_ >>

UpdateTip(self) == /\ pc[self] = "UpdateTip"
                   /\ the_network' = [the_network EXCEPT ![self].chain_tip =                                [
                                                                                 height |-> blocks_data[self][Len(blocks_data[self])].height,
                                                                                 hash |-> blocks_data[self][Len(blocks_data[self])].hash
                                                                             ]]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ blocks_data' = [blocks_data EXCEPT ![self] = Head(stack[self]).blocks_data]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << channels, id_a, found_blocks, hash_count, 
                                   block_header_hashes, remote_peer_blocks, 
                                   start_height, end_height, hashes, id, id_ >>

getdata(self) == Incorporate(self) \/ UpdateTip(self)

Listening(self) == /\ pc[self] = "Listening"
                   /\ Assert(Len(the_network) >= self /\ Len(channels) >= self, 
                             "Failure of assertion at line 158, column 9.")
                   /\ IF channels[self].header = defaultInitValue
                         THEN /\ pc' = [pc EXCEPT ![self] = "Listening"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Requests"]
                   /\ UNCHANGED << the_network, channels, stack, id_a, 
                                   found_blocks, hash_count, 
                                   block_header_hashes, remote_peer_blocks, 
                                   start_height, end_height, hashes, id, 
                                   blocks_data, id_ >>

Requests(self) == /\ pc[self] = "Requests"
                  /\ LET command == channels[self].header.command_name IN
                       IF command = "addr"
                          THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addr",
                                                                        pc        |->  "Listening" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "SendVersionMsg"]
                               /\ UNCHANGED << found_blocks, hash_count, 
                                               block_header_hashes, 
                                               remote_peer_blocks, 
                                               start_height, end_height, 
                                               blocks_data >>
                          ELSE /\ IF command = "version"
                                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "version",
                                                                                   pc        |->  "Listening" ] >>
                                                                               \o stack[self]]
                                          /\ pc' = [pc EXCEPT ![self] = "HandleVersionMsg"]
                                          /\ UNCHANGED << found_blocks, 
                                                          hash_count, 
                                                          block_header_hashes, 
                                                          remote_peer_blocks, 
                                                          start_height, 
                                                          end_height, 
                                                          blocks_data >>
                                     ELSE /\ IF command = "verack"
                                                THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "verack",
                                                                                              pc        |->  "ClientTaskLoop" ] >>
                                                                                          \o stack[self]]
                                                     /\ pc' = [pc EXCEPT ![self] = "HandleVerackMsg"]
                                                     /\ UNCHANGED << found_blocks, 
                                                                     hash_count, 
                                                                     block_header_hashes, 
                                                                     remote_peer_blocks, 
                                                                     start_height, 
                                                                     end_height, 
                                                                     blocks_data >>
                                                ELSE /\ IF command = "getblocks"
                                                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getblocks",
                                                                                                         pc        |->  "Listening",
                                                                                                         found_blocks |->  found_blocks[self],
                                                                                                         hash_count |->  hash_count[self],
                                                                                                         block_header_hashes |->  block_header_hashes[self],
                                                                                                         remote_peer_blocks |->  remote_peer_blocks[self],
                                                                                                         start_height |->  start_height[self],
                                                                                                         end_height |->  end_height[self] ] >>
                                                                                                     \o stack[self]]
                                                                /\ found_blocks' = [found_blocks EXCEPT ![self] = defaultInitValue]
                                                                /\ hash_count' = [hash_count EXCEPT ![self] = defaultInitValue]
                                                                /\ block_header_hashes' = [block_header_hashes EXCEPT ![self] = defaultInitValue]
                                                                /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = defaultInitValue]
                                                                /\ start_height' = [start_height EXCEPT ![self] = defaultInitValue]
                                                                /\ end_height' = [end_height EXCEPT ![self] = defaultInitValue]
                                                                /\ pc' = [pc EXCEPT ![self] = "HandleGetBlocksMsg"]
                                                                /\ UNCHANGED blocks_data
                                                           ELSE /\ IF command = "inv"
                                                                      THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "inv",
                                                                                                                    pc        |->  "Listening" ] >>
                                                                                                                \o stack[self]]
                                                                           /\ pc' = [pc EXCEPT ![self] = "SendGetDataMsg"]
                                                                           /\ UNCHANGED blocks_data
                                                                      ELSE /\ IF command = "getdata"
                                                                                 THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getdata",
                                                                                                                               pc        |->  "ClientTaskLoop",
                                                                                                                               blocks_data |->  blocks_data[self] ] >>
                                                                                                                           \o stack[self]]
                                                                                      /\ blocks_data' = [blocks_data EXCEPT ![self] = defaultInitValue]
                                                                                      /\ pc' = [pc EXCEPT ![self] = "Incorporate"]
                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ClientTaskLoop"]
                                                                                      /\ UNCHANGED << stack, 
                                                                                                      blocks_data >>
                                                                /\ UNCHANGED << found_blocks, 
                                                                                hash_count, 
                                                                                block_header_hashes, 
                                                                                remote_peer_blocks, 
                                                                                start_height, 
                                                                                end_height >>
                  /\ UNCHANGED << the_network, channels, id_a, hashes, id, id_ >>

ClientTaskLoop(self) == /\ pc[self] = "ClientTaskLoop"
                        /\ channels' = [channels EXCEPT ![self] = [header |-> defaultInitValue, payload |-> defaultInitValue]]
                        /\ pc' = [pc EXCEPT ![self] = "Listening"]
                        /\ UNCHANGED << the_network, stack, id_a, found_blocks, 
                                        hash_count, block_header_hashes, 
                                        remote_peer_blocks, start_height, 
                                        end_height, hashes, id, blocks_data, 
                                        id_ >>

LISTEN(self) == Listening(self) \/ Requests(self) \/ ClientTaskLoop(self)

Announce(self) == /\ pc[self] = "Announce"
                  /\ Len(the_network[id_[self]].peer_set) = 1
                  /\ /\ id_a' = [id_a EXCEPT ![self] = id_[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "announce",
                                                              pc        |->  "RequestInventory",
                                                              id_a      |->  id_a[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "SendAddrMsg"]
                  /\ UNCHANGED << the_network, channels, found_blocks, 
                                  hash_count, block_header_hashes, 
                                  remote_peer_blocks, start_height, end_height, 
                                  hashes, id, blocks_data, id_ >>

RequestInventory(self) == /\ pc[self] = "RequestInventory"
                          /\ Len(the_network[id_[self]].peer_set) > 0 /\ the_network[id_[self]].peer_set[1].established = TRUE
                          /\ pc' = [pc EXCEPT ![self] = "Syncronizer"]
                          /\ UNCHANGED << the_network, channels, stack, id_a, 
                                          found_blocks, hash_count, 
                                          block_header_hashes, 
                                          remote_peer_blocks, start_height, 
                                          end_height, hashes, id, blocks_data, 
                                          id_ >>

Syncronizer(self) == /\ pc[self] = "Syncronizer"
                     /\ IF the_network[id_[self]].chain_tip.height < the_network[id_[self]].peer_set[1].tip
                           THEN /\ channels[id_[self]].header = defaultInitValue /\ channels[id_[self]].payload = defaultInitValue
                                /\ IF the_network[id_[self]].chain_tip.height = 0
                                      THEN /\ /\ hashes' = [hashes EXCEPT ![self] = <<>>]
                                              /\ id' = [id EXCEPT ![self] = id_[self]]
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                       pc        |->  "Syncronizer",
                                                                                       hashes    |->  hashes[self],
                                                                                       id        |->  id[self] ] >>
                                                                                   \o stack[self]]
                                           /\ pc' = [pc EXCEPT ![self] = "SendGetBlocksMsg"]
                                      ELSE /\ /\ hashes' = [hashes EXCEPT ![self] = <<the_network[id_[self]].chain_tip.hash>>]
                                              /\ id' = [id EXCEPT ![self] = id_[self]]
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                       pc        |->  "Syncronizer",
                                                                                       hashes    |->  hashes[self],
                                                                                       id        |->  id[self] ] >>
                                                                                   \o stack[self]]
                                           /\ pc' = [pc EXCEPT ![self] = "SendGetBlocksMsg"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "CheckSync"]
                                /\ UNCHANGED << stack, hashes, id >>
                     /\ UNCHANGED << the_network, channels, id_a, found_blocks, 
                                     hash_count, block_header_hashes, 
                                     remote_peer_blocks, start_height, 
                                     end_height, blocks_data, id_ >>

CheckSync(self) == /\ pc[self] = "CheckSync"
                   /\ channels[id_[self]].header = defaultInitValue /\ channels[id_[self]].payload = defaultInitValue
                   /\ the_network[id_[self]].peer_set[1].tip = the_network[id_[self]].chain_tip.height
                   /\ PrintT("Peer is in sync!")
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << the_network, channels, stack, id_a, 
                                   found_blocks, hash_count, 
                                   block_header_hashes, remote_peer_blocks, 
                                   start_height, end_height, hashes, id, 
                                   blocks_data, id_ >>

SYNC(self) == Announce(self) \/ RequestInventory(self) \/ Syncronizer(self)
                 \/ CheckSync(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ announce(self) \/ addr(self)
                               \/ version(self) \/ verack(self)
                               \/ getblocks(self) \/ request_blocks(self)
                               \/ inv(self) \/ getdata(self))
           \/ (\E self \in 1 .. Len(PEERS): LISTEN(self))
           \/ (\E self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(PEERS): SYNC(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
