-------------------------------- MODULE p2p ---------------------------------
(***************************************************************************)
(* This module defines a simple peer-to-peer network protocol that allows  *)
(* peers to connect, exchange blocks, and synchronize their chains.        *)
(***************************************************************************)
EXTENDS TLC, Sequences, Naturals, FiniteSets, Utils, Blockchain

\* Define the network to be used by the algorithm.
CONSTANT RunningBlockchain

\* Maximum number of blocks to be retrieved in a single getblocks response.
CONSTANT MaxGetBlocksInvResponse

\* Maximum number of outbound connections a peer can have.
CONSTANT MaxConnectionsPerPeer

\* Difference in the SYNCHRONIZER process id so that it does not conflict with the LISTENER one.
PeerProcessDiffId == 1000

-----------------------------------------------------------------------------

(*--algorithm p2p

variables
    \* Represent the whole universe of peers in the network with all of their data.
    the_network = RunningBlockchain;

    \* Each peer has a channel to communicate with other peers. Number of connections is limited.
    channels = [i \in 1..Len(the_network) |->
        [j \in 1..MaxConnectionsPerPeer |-> [
            header |-> defaultInitValue,
            payload |-> defaultInitValue
        ]]
    ];

define
    \* Import the operators used in the algorithm.
    LOCAL Ops == INSTANCE Operators
end define;

\* Announce the intention of a peer to connect with another in the network by sending an `addr` message.
procedure announce(local_peer_id, remote_peer_id)
begin
    SendAddrMsg:
        channels[local_peer_id][remote_peer_id] := [
            header |-> [command_name |-> "addr"],
            payload |-> [
                address_count |-> 1,
                \* Only a single address is supported.
                addresses |-> the_network[local_peer_id].peer
            ]
        ];
    return;
end procedure;

\* Given that an `addr` message is received, send a `version` message from the remote peer to start the connection.
procedure addr(local_peer_id, remote_peer_id)
begin
    SendVersionMsg:
        channels[local_peer_id][remote_peer_id] := [
            header |-> [command_name |-> "version"],
            payload |-> [
                addr_recv |-> the_network[local_peer_id].peer,
                addr_trans |-> the_network[local_peer_id].peer_set[remote_peer_id].address,
                start_height |-> 
                    Ops!GetPeerTip(the_network[local_peer_id].peer_set[remote_peer_id].address)]
        ];
    return;
end procedure;

\* Given a `version` message is received, send `verack` to acknowledge the connection.
procedure version(local_peer_id, remote_peer_id)
begin
    HandleVersionMsg:
        the_network[local_peer_id].peer_set[remote_peer_id].tip :=
            channels[local_peer_id][remote_peer_id].payload.start_height;
    SendVerackMsg:
        channels[local_peer_id][remote_peer_id] := [
            header |-> [command_name |-> "verack"],
            payload |-> defaultInitValue
        ];
    return;
end procedure;

\* Given a `verack` message is received, establish the connection.
procedure verack(local_peer_id, remote_peer_id)
begin
    HandleVerackMsg:
        the_network[local_peer_id].peer_set[remote_peer_id].established := TRUE;
    return;
end procedure;

\* Given a `getblocks` message is received, send an `inv` message with the blocks requested.
procedure getblocks(local_peer_id, remote_peer_id)
variables 
    found_blocks, hash_count, block_header_hashes, remote_peer_blocks, start_height, end_height;
begin
    HandleGetBlocksMsg:
        \* Retrieve necessary values from the channel payload
        hash_count := channels[local_peer_id][remote_peer_id].payload.hash_count;
        block_header_hashes := channels[local_peer_id][remote_peer_id].payload.block_header_hashes;

        \* Fetch the blocks of the remote peer
        remote_peer_blocks := 
            Ops!GetPeerBlocks(the_network[local_peer_id].peer_set[remote_peer_id].address);

        \* Determine the range of blocks to retrieve
        if hash_count = 0 then
            start_height := 1;
        else
            \* Assuming the hashes are in order, the height of the first hash should be the tip, ignore the rest. 
            start_height := 
                Ops!FindBlockByHash(remote_peer_blocks, block_header_hashes[1]).height + 1;
        end if;
        end_height := start_height + (MaxGetBlocksInvResponse - 1);

        \* Find the blocks within the specified range.
        found_blocks := Ops!FindBlocks(remote_peer_blocks, start_height, end_height);
    SendInvMsg:
        channels[local_peer_id][remote_peer_id] := [
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
procedure request_blocks(hashes, local_peer_id, remote_peer_id)
begin
    SendGetBlocksMsg:
        channels[local_peer_id][remote_peer_id] := [
            header |-> [command_name |-> "getblocks"],
            payload |-> [
                hash_count |-> Len(hashes),
                block_header_hashes |-> hashes]
        ];
    return;
end procedure;

\* Given an `inv` message is received, send a `getdata` message to request the blocks.
procedure inv(local_peer_id, remote_peer_id)
begin
    SendGetDataMsg:
        channels[local_peer_id][remote_peer_id] := [
            header |-> [command_name |-> "getdata"],
            payload |-> channels[local_peer_id][remote_peer_id].payload
        ];
    return;
end procedure;

\* Incorporate data to the local peer from the inventory received.
procedure getdata(local_peer_id, remote_peer_id)
variables blocks_data;
begin
    Incorporate:
        blocks_data := [item \in 1..Len(channels[local_peer_id][remote_peer_id].payload.inventory) |->
            Ops!FindBlockByHash(
                Ops!GetPeerBlocks(the_network[local_peer_id].peer_set[remote_peer_id].address),
                channels[local_peer_id][remote_peer_id].payload.inventory[item].hash
            )
        ];
        the_network[local_peer_id].blocks := the_network[local_peer_id].blocks \cup ToSet(blocks_data);
    UpdateTip:
        the_network[local_peer_id].chain_tip := [
            height |-> blocks_data[Len(blocks_data)].height,
            hash |-> blocks_data[Len(blocks_data)].hash
        ];
    return;
end procedure;

\* A set of listener process for each peer to listen to incoming messages and act accordingly.
process LISTENER \in 1 .. Len(RunningBlockchain)
variables command;
begin
    Listening:
        await Len(the_network) >= 2;
        with remote_peer_index \in 1..Len(the_network[self].peer_set) do
            if channels[self][remote_peer_index].header = defaultInitValue then
                goto Listening;
            end if;
        end with;
    Requests:
        with remote_peer_index \in 1..Len(the_network[self].peer_set) do
            await channels[self][remote_peer_index].header # defaultInitValue;
            command := channels[self][remote_peer_index].header.command_name;
            if command = "addr" then
                call addr(self, remote_peer_index);
                goto Listening;
            elsif command = "version" then
                call version(self, remote_peer_index);
                goto Listening;
            elsif command = "verack" then
                call verack(self, remote_peer_index);
            elsif command = "getblocks" then
                call getblocks(self, remote_peer_index);
                goto Listening;
            elsif command = "inv" then
                call inv(self, remote_peer_index);
                goto Listening;
            elsif command = "getdata" then
                call getdata(self, remote_peer_index);
            end if;
        end with;
    ListenerLoop:
        with remote_peer_index \in 1..Len(the_network[self].peer_set) do
            channels[self][remote_peer_index] := 
                [header |-> defaultInitValue, payload |-> defaultInitValue];
            goto Listening;
        end with;
end process;

\* A set of processes to synchronize each peer with the network.
process SYNCHRONIZER \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(RunningBlockchain)
variables local_peer_index = self - PeerProcessDiffId, best_tip = 0;
begin
    Announce:
        \* The network must have at least two peer.
        assert Len(the_network) >= 2;

        \* The peer set size must be at least 1, ignoring the peers that are seeders only.
        await Len(the_network[local_peer_index].peer_set) > 0;

        \* Connect to each available peer we have.    
        with remote_peer_index \in 1..Len(the_network[local_peer_index].peer_set) do
            call announce(local_peer_index, remote_peer_index);
        end with;
    RequestInventory:
        with remote_peer_index \in 1..Len(the_network[local_peer_index].peer_set) do
            \* Make sure the connection is established before requesting any block from this peer.
            await the_network[local_peer_index].peer_set[remote_peer_index].established = TRUE;

            \* Find the best tip among all peers.
            if the_network[local_peer_index].peer_set[remote_peer_index].tip > best_tip then
                best_tip := the_network[local_peer_index].peer_set[remote_peer_index].tip;
            end if;
            
            \* Wait for the peer channel to be empty before requesting new blocks.
            await channels[local_peer_index][remote_peer_index].header = defaultInitValue
                /\ channels[local_peer_index][remote_peer_index].payload = defaultInitValue;

            \* Check if the local peer is behind the remote peer.
            if the_network[local_peer_index].chain_tip.height <
                the_network[local_peer_index].peer_set[remote_peer_index].tip then
                \* Request blocks.
                if the_network[local_peer_index].chain_tip.height = 0 then
                    call request_blocks(<<>>, local_peer_index, remote_peer_index);
                else
                    call request_blocks(
                        <<the_network[local_peer_index].chain_tip.hash>>,
                        local_peer_index,
                        remote_peer_index
                    );
                end if;
            end if;
        end with;
    CheckSync:
        await the_network[local_peer_index].chain_tip.height > 0;
        if the_network[local_peer_index].chain_tip.height < best_tip then
            goto RequestInventory;
        else
            \* Make sure all connections are still established and all communication channels are empty
            with remote_peer_index \in 1..Len(the_network[local_peer_index].peer_set) do
                await the_network[local_peer_index].peer_set[remote_peer_index].established = TRUE
                    /\ channels[local_peer_index][remote_peer_index].header = defaultInitValue 
                    /\ channels[local_peer_index][remote_peer_index].payload = defaultInitValue;
            end with;
            print "Peer is in sync!";
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6acb42eb" /\ chksum(tla) = "4e4ceef9")
\* Parameter local_peer_id of procedure announce at line 40 col 20 changed to local_peer_id_
\* Parameter remote_peer_id of procedure announce at line 40 col 35 changed to remote_peer_id_
\* Parameter local_peer_id of procedure addr at line 55 col 16 changed to local_peer_id_a
\* Parameter remote_peer_id of procedure addr at line 55 col 31 changed to remote_peer_id_a
\* Parameter local_peer_id of procedure version at line 70 col 19 changed to local_peer_id_v
\* Parameter remote_peer_id of procedure version at line 70 col 34 changed to remote_peer_id_v
\* Parameter local_peer_id of procedure verack at line 84 col 18 changed to local_peer_id_ve
\* Parameter remote_peer_id of procedure verack at line 84 col 33 changed to remote_peer_id_ve
\* Parameter local_peer_id of procedure getblocks at line 92 col 21 changed to local_peer_id_g
\* Parameter remote_peer_id of procedure getblocks at line 92 col 36 changed to remote_peer_id_g
\* Parameter local_peer_id of procedure request_blocks at line 134 col 34 changed to local_peer_id_r
\* Parameter remote_peer_id of procedure request_blocks at line 134 col 49 changed to remote_peer_id_r
\* Parameter local_peer_id of procedure inv at line 147 col 15 changed to local_peer_id_i
\* Parameter remote_peer_id of procedure inv at line 147 col 30 changed to remote_peer_id_i
CONSTANT defaultInitValue
VARIABLES the_network, channels, pc, stack

(* define statement *)
LOCAL Ops == INSTANCE Operators

VARIABLES local_peer_id_, remote_peer_id_, local_peer_id_a, remote_peer_id_a, 
          local_peer_id_v, remote_peer_id_v, local_peer_id_ve, 
          remote_peer_id_ve, local_peer_id_g, remote_peer_id_g, found_blocks, 
          hash_count, block_header_hashes, remote_peer_blocks, start_height, 
          end_height, hashes, local_peer_id_r, remote_peer_id_r, 
          local_peer_id_i, remote_peer_id_i, local_peer_id, remote_peer_id, 
          blocks_data, command, local_peer_index, best_tip

vars == << the_network, channels, pc, stack, local_peer_id_, remote_peer_id_, 
           local_peer_id_a, remote_peer_id_a, local_peer_id_v, 
           remote_peer_id_v, local_peer_id_ve, remote_peer_id_ve, 
           local_peer_id_g, remote_peer_id_g, found_blocks, hash_count, 
           block_header_hashes, remote_peer_blocks, start_height, end_height, 
           hashes, local_peer_id_r, remote_peer_id_r, local_peer_id_i, 
           remote_peer_id_i, local_peer_id, remote_peer_id, blocks_data, 
           command, local_peer_index, best_tip >>

ProcSet == (1 .. Len(RunningBlockchain)) \cup (PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(RunningBlockchain))

Init == (* Global variables *)
        /\ the_network = RunningBlockchain
        /\ channels =            [i \in 1..Len(the_network) |->
                          [j \in 1..MaxConnectionsPerPeer |-> [
                              header |-> defaultInitValue,
                              payload |-> defaultInitValue
                          ]]
                      ]
        (* Procedure announce *)
        /\ local_peer_id_ = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure addr *)
        /\ local_peer_id_a = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_a = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure version *)
        /\ local_peer_id_v = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_v = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure verack *)
        /\ local_peer_id_ve = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_ve = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getblocks *)
        /\ local_peer_id_g = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_g = [ self \in ProcSet |-> defaultInitValue]
        /\ found_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ hash_count = [ self \in ProcSet |-> defaultInitValue]
        /\ block_header_hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_blocks = [ self \in ProcSet |-> defaultInitValue]
        /\ start_height = [ self \in ProcSet |-> defaultInitValue]
        /\ end_height = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure request_blocks *)
        /\ hashes = [ self \in ProcSet |-> defaultInitValue]
        /\ local_peer_id_r = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure inv *)
        /\ local_peer_id_i = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id_i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure getdata *)
        /\ local_peer_id = [ self \in ProcSet |-> defaultInitValue]
        /\ remote_peer_id = [ self \in ProcSet |-> defaultInitValue]
        /\ blocks_data = [ self \in ProcSet |-> defaultInitValue]
        (* Process LISTENER *)
        /\ command = [self \in 1 .. Len(RunningBlockchain) |-> defaultInitValue]
        (* Process SYNCHRONIZER *)
        /\ local_peer_index = [self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(RunningBlockchain) |-> self - PeerProcessDiffId]
        /\ best_tip = [self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(RunningBlockchain) |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1 .. Len(RunningBlockchain) -> "Listening"
                                        [] self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(RunningBlockchain) -> "Announce"]

SendAddrMsg(self) == /\ pc[self] = "SendAddrMsg"
                     /\ channels' = [channels EXCEPT ![local_peer_id_[self]][remote_peer_id_[self]] =                                            [
                                                                                                          header |-> [command_name |-> "addr"],
                                                                                                          payload |-> [
                                                                                                              address_count |-> 1,
                                                                                                      
                                                                                                              addresses |-> the_network[local_peer_id_[self]].peer
                                                                                                          ]
                                                                                                      ]]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ local_peer_id_' = [local_peer_id_ EXCEPT ![self] = Head(stack[self]).local_peer_id_]
                     /\ remote_peer_id_' = [remote_peer_id_ EXCEPT ![self] = Head(stack[self]).remote_peer_id_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << the_network, local_peer_id_a, 
                                     remote_peer_id_a, local_peer_id_v, 
                                     remote_peer_id_v, local_peer_id_ve, 
                                     remote_peer_id_ve, local_peer_id_g, 
                                     remote_peer_id_g, found_blocks, 
                                     hash_count, block_header_hashes, 
                                     remote_peer_blocks, start_height, 
                                     end_height, hashes, local_peer_id_r, 
                                     remote_peer_id_r, local_peer_id_i, 
                                     remote_peer_id_i, local_peer_id, 
                                     remote_peer_id, blocks_data, command, 
                                     local_peer_index, best_tip >>

announce(self) == SendAddrMsg(self)

SendVersionMsg(self) == /\ pc[self] = "SendVersionMsg"
                        /\ channels' = [channels EXCEPT ![local_peer_id_a[self]][remote_peer_id_a[self]] =                                            [
                                                                                                               header |-> [command_name |-> "version"],
                                                                                                               payload |-> [
                                                                                                                   addr_recv |-> the_network[local_peer_id_a[self]].peer,
                                                                                                                   addr_trans |-> the_network[local_peer_id_a[self]].peer_set[remote_peer_id_a[self]].address,
                                                                                                                   start_height |->
                                                                                                                       Ops!GetPeerTip(the_network[local_peer_id_a[self]].peer_set[remote_peer_id_a[self]].address)]
                                                                                                           ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ local_peer_id_a' = [local_peer_id_a EXCEPT ![self] = Head(stack[self]).local_peer_id_a]
                        /\ remote_peer_id_a' = [remote_peer_id_a EXCEPT ![self] = Head(stack[self]).remote_peer_id_a]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, local_peer_id_, 
                                        remote_peer_id_, local_peer_id_v, 
                                        remote_peer_id_v, local_peer_id_ve, 
                                        remote_peer_id_ve, local_peer_id_g, 
                                        remote_peer_id_g, found_blocks, 
                                        hash_count, block_header_hashes, 
                                        remote_peer_blocks, start_height, 
                                        end_height, hashes, local_peer_id_r, 
                                        remote_peer_id_r, local_peer_id_i, 
                                        remote_peer_id_i, local_peer_id, 
                                        remote_peer_id, blocks_data, command, 
                                        local_peer_index, best_tip >>

addr(self) == SendVersionMsg(self)

HandleVersionMsg(self) == /\ pc[self] = "HandleVersionMsg"
                          /\ the_network' = [the_network EXCEPT ![local_peer_id_v[self]].peer_set[remote_peer_id_v[self]].tip = channels[local_peer_id_v[self]][remote_peer_id_v[self]].payload.start_height]
                          /\ pc' = [pc EXCEPT ![self] = "SendVerackMsg"]
                          /\ UNCHANGED << channels, stack, local_peer_id_, 
                                          remote_peer_id_, local_peer_id_a, 
                                          remote_peer_id_a, local_peer_id_v, 
                                          remote_peer_id_v, local_peer_id_ve, 
                                          remote_peer_id_ve, local_peer_id_g, 
                                          remote_peer_id_g, found_blocks, 
                                          hash_count, block_header_hashes, 
                                          remote_peer_blocks, start_height, 
                                          end_height, hashes, local_peer_id_r, 
                                          remote_peer_id_r, local_peer_id_i, 
                                          remote_peer_id_i, local_peer_id, 
                                          remote_peer_id, blocks_data, command, 
                                          local_peer_index, best_tip >>

SendVerackMsg(self) == /\ pc[self] = "SendVerackMsg"
                       /\ channels' = [channels EXCEPT ![local_peer_id_v[self]][remote_peer_id_v[self]] =                                            [
                                                                                                              header |-> [command_name |-> "verack"],
                                                                                                              payload |-> defaultInitValue
                                                                                                          ]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ local_peer_id_v' = [local_peer_id_v EXCEPT ![self] = Head(stack[self]).local_peer_id_v]
                       /\ remote_peer_id_v' = [remote_peer_id_v EXCEPT ![self] = Head(stack[self]).remote_peer_id_v]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << the_network, local_peer_id_, 
                                       remote_peer_id_, local_peer_id_a, 
                                       remote_peer_id_a, local_peer_id_ve, 
                                       remote_peer_id_ve, local_peer_id_g, 
                                       remote_peer_id_g, found_blocks, 
                                       hash_count, block_header_hashes, 
                                       remote_peer_blocks, start_height, 
                                       end_height, hashes, local_peer_id_r, 
                                       remote_peer_id_r, local_peer_id_i, 
                                       remote_peer_id_i, local_peer_id, 
                                       remote_peer_id, blocks_data, command, 
                                       local_peer_index, best_tip >>

version(self) == HandleVersionMsg(self) \/ SendVerackMsg(self)

HandleVerackMsg(self) == /\ pc[self] = "HandleVerackMsg"
                         /\ the_network' = [the_network EXCEPT ![local_peer_id_ve[self]].peer_set[remote_peer_id_ve[self]].established = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ local_peer_id_ve' = [local_peer_id_ve EXCEPT ![self] = Head(stack[self]).local_peer_id_ve]
                         /\ remote_peer_id_ve' = [remote_peer_id_ve EXCEPT ![self] = Head(stack[self]).remote_peer_id_ve]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << channels, local_peer_id_, 
                                         remote_peer_id_, local_peer_id_a, 
                                         remote_peer_id_a, local_peer_id_v, 
                                         remote_peer_id_v, local_peer_id_g, 
                                         remote_peer_id_g, found_blocks, 
                                         hash_count, block_header_hashes, 
                                         remote_peer_blocks, start_height, 
                                         end_height, hashes, local_peer_id_r, 
                                         remote_peer_id_r, local_peer_id_i, 
                                         remote_peer_id_i, local_peer_id, 
                                         remote_peer_id, blocks_data, command, 
                                         local_peer_index, best_tip >>

verack(self) == HandleVerackMsg(self)

HandleGetBlocksMsg(self) == /\ pc[self] = "HandleGetBlocksMsg"
                            /\ hash_count' = [hash_count EXCEPT ![self] = channels[local_peer_id_g[self]][remote_peer_id_g[self]].payload.hash_count]
                            /\ block_header_hashes' = [block_header_hashes EXCEPT ![self] = channels[local_peer_id_g[self]][remote_peer_id_g[self]].payload.block_header_hashes]
                            /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = Ops!GetPeerBlocks(the_network[local_peer_id_g[self]].peer_set[remote_peer_id_g[self]].address)]
                            /\ IF hash_count'[self] = 0
                                  THEN /\ start_height' = [start_height EXCEPT ![self] = 1]
                                  ELSE /\ start_height' = [start_height EXCEPT ![self] = Ops!FindBlockByHash(remote_peer_blocks'[self], block_header_hashes'[self][1]).height + 1]
                            /\ end_height' = [end_height EXCEPT ![self] = start_height'[self] + (MaxGetBlocksInvResponse - 1)]
                            /\ found_blocks' = [found_blocks EXCEPT ![self] = Ops!FindBlocks(remote_peer_blocks'[self], start_height'[self], end_height'[self])]
                            /\ pc' = [pc EXCEPT ![self] = "SendInvMsg"]
                            /\ UNCHANGED << the_network, channels, stack, 
                                            local_peer_id_, remote_peer_id_, 
                                            local_peer_id_a, remote_peer_id_a, 
                                            local_peer_id_v, remote_peer_id_v, 
                                            local_peer_id_ve, 
                                            remote_peer_id_ve, local_peer_id_g, 
                                            remote_peer_id_g, hashes, 
                                            local_peer_id_r, remote_peer_id_r, 
                                            local_peer_id_i, remote_peer_id_i, 
                                            local_peer_id, remote_peer_id, 
                                            blocks_data, command, 
                                            local_peer_index, best_tip >>

SendInvMsg(self) == /\ pc[self] = "SendInvMsg"
                    /\ channels' = [channels EXCEPT ![local_peer_id_g[self]][remote_peer_id_g[self]] =                                            [
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
                    /\ local_peer_id_g' = [local_peer_id_g EXCEPT ![self] = Head(stack[self]).local_peer_id_g]
                    /\ remote_peer_id_g' = [remote_peer_id_g EXCEPT ![self] = Head(stack[self]).remote_peer_id_g]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << the_network, local_peer_id_, 
                                    remote_peer_id_, local_peer_id_a, 
                                    remote_peer_id_a, local_peer_id_v, 
                                    remote_peer_id_v, local_peer_id_ve, 
                                    remote_peer_id_ve, hashes, local_peer_id_r, 
                                    remote_peer_id_r, local_peer_id_i, 
                                    remote_peer_id_i, local_peer_id, 
                                    remote_peer_id, blocks_data, command, 
                                    local_peer_index, best_tip >>

getblocks(self) == HandleGetBlocksMsg(self) \/ SendInvMsg(self)

SendGetBlocksMsg(self) == /\ pc[self] = "SendGetBlocksMsg"
                          /\ channels' = [channels EXCEPT ![local_peer_id_r[self]][remote_peer_id_r[self]] =                                            [
                                                                                                                 header |-> [command_name |-> "getblocks"],
                                                                                                                 payload |-> [
                                                                                                                     hash_count |-> Len(hashes[self]),
                                                                                                                     block_header_hashes |-> hashes[self]]
                                                                                                             ]]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ hashes' = [hashes EXCEPT ![self] = Head(stack[self]).hashes]
                          /\ local_peer_id_r' = [local_peer_id_r EXCEPT ![self] = Head(stack[self]).local_peer_id_r]
                          /\ remote_peer_id_r' = [remote_peer_id_r EXCEPT ![self] = Head(stack[self]).remote_peer_id_r]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << the_network, local_peer_id_, 
                                          remote_peer_id_, local_peer_id_a, 
                                          remote_peer_id_a, local_peer_id_v, 
                                          remote_peer_id_v, local_peer_id_ve, 
                                          remote_peer_id_ve, local_peer_id_g, 
                                          remote_peer_id_g, found_blocks, 
                                          hash_count, block_header_hashes, 
                                          remote_peer_blocks, start_height, 
                                          end_height, local_peer_id_i, 
                                          remote_peer_id_i, local_peer_id, 
                                          remote_peer_id, blocks_data, command, 
                                          local_peer_index, best_tip >>

request_blocks(self) == SendGetBlocksMsg(self)

SendGetDataMsg(self) == /\ pc[self] = "SendGetDataMsg"
                        /\ channels' = [channels EXCEPT ![local_peer_id_i[self]][remote_peer_id_i[self]] =                                            [
                                                                                                               header |-> [command_name |-> "getdata"],
                                                                                                               payload |-> channels[local_peer_id_i[self]][remote_peer_id_i[self]].payload
                                                                                                           ]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ local_peer_id_i' = [local_peer_id_i EXCEPT ![self] = Head(stack[self]).local_peer_id_i]
                        /\ remote_peer_id_i' = [remote_peer_id_i EXCEPT ![self] = Head(stack[self]).remote_peer_id_i]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << the_network, local_peer_id_, 
                                        remote_peer_id_, local_peer_id_a, 
                                        remote_peer_id_a, local_peer_id_v, 
                                        remote_peer_id_v, local_peer_id_ve, 
                                        remote_peer_id_ve, local_peer_id_g, 
                                        remote_peer_id_g, found_blocks, 
                                        hash_count, block_header_hashes, 
                                        remote_peer_blocks, start_height, 
                                        end_height, hashes, local_peer_id_r, 
                                        remote_peer_id_r, local_peer_id, 
                                        remote_peer_id, blocks_data, command, 
                                        local_peer_index, best_tip >>

inv(self) == SendGetDataMsg(self)

Incorporate(self) == /\ pc[self] = "Incorporate"
                     /\ blocks_data' = [blocks_data EXCEPT ![self] =                [item \in 1..Len(channels[local_peer_id[self]][remote_peer_id[self]].payload.inventory) |->
                                                                         Ops!FindBlockByHash(
                                                                             Ops!GetPeerBlocks(the_network[local_peer_id[self]].peer_set[remote_peer_id[self]].address),
                                                                             channels[local_peer_id[self]][remote_peer_id[self]].payload.inventory[item].hash
                                                                         )
                                                                     ]]
                     /\ the_network' = [the_network EXCEPT ![local_peer_id[self]].blocks = the_network[local_peer_id[self]].blocks \cup ToSet(blocks_data'[self])]
                     /\ pc' = [pc EXCEPT ![self] = "UpdateTip"]
                     /\ UNCHANGED << channels, stack, local_peer_id_, 
                                     remote_peer_id_, local_peer_id_a, 
                                     remote_peer_id_a, local_peer_id_v, 
                                     remote_peer_id_v, local_peer_id_ve, 
                                     remote_peer_id_ve, local_peer_id_g, 
                                     remote_peer_id_g, found_blocks, 
                                     hash_count, block_header_hashes, 
                                     remote_peer_blocks, start_height, 
                                     end_height, hashes, local_peer_id_r, 
                                     remote_peer_id_r, local_peer_id_i, 
                                     remote_peer_id_i, local_peer_id, 
                                     remote_peer_id, command, local_peer_index, 
                                     best_tip >>

UpdateTip(self) == /\ pc[self] = "UpdateTip"
                   /\ the_network' = [the_network EXCEPT ![local_peer_id[self]].chain_tip =                                         [
                                                                                                height |-> blocks_data[self][Len(blocks_data[self])].height,
                                                                                                hash |-> blocks_data[self][Len(blocks_data[self])].hash
                                                                                            ]]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ blocks_data' = [blocks_data EXCEPT ![self] = Head(stack[self]).blocks_data]
                   /\ local_peer_id' = [local_peer_id EXCEPT ![self] = Head(stack[self]).local_peer_id]
                   /\ remote_peer_id' = [remote_peer_id EXCEPT ![self] = Head(stack[self]).remote_peer_id]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << channels, local_peer_id_, remote_peer_id_, 
                                   local_peer_id_a, remote_peer_id_a, 
                                   local_peer_id_v, remote_peer_id_v, 
                                   local_peer_id_ve, remote_peer_id_ve, 
                                   local_peer_id_g, remote_peer_id_g, 
                                   found_blocks, hash_count, 
                                   block_header_hashes, remote_peer_blocks, 
                                   start_height, end_height, hashes, 
                                   local_peer_id_r, remote_peer_id_r, 
                                   local_peer_id_i, remote_peer_id_i, command, 
                                   local_peer_index, best_tip >>

getdata(self) == Incorporate(self) \/ UpdateTip(self)

Listening(self) == /\ pc[self] = "Listening"
                   /\ Len(the_network) >= 2
                   /\ \E remote_peer_index \in 1..Len(the_network[self].peer_set):
                        IF channels[self][remote_peer_index].header = defaultInitValue
                           THEN /\ pc' = [pc EXCEPT ![self] = "Listening"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Requests"]
                   /\ UNCHANGED << the_network, channels, stack, 
                                   local_peer_id_, remote_peer_id_, 
                                   local_peer_id_a, remote_peer_id_a, 
                                   local_peer_id_v, remote_peer_id_v, 
                                   local_peer_id_ve, remote_peer_id_ve, 
                                   local_peer_id_g, remote_peer_id_g, 
                                   found_blocks, hash_count, 
                                   block_header_hashes, remote_peer_blocks, 
                                   start_height, end_height, hashes, 
                                   local_peer_id_r, remote_peer_id_r, 
                                   local_peer_id_i, remote_peer_id_i, 
                                   local_peer_id, remote_peer_id, blocks_data, 
                                   command, local_peer_index, best_tip >>

Requests(self) == /\ pc[self] = "Requests"
                  /\ \E remote_peer_index \in 1..Len(the_network[self].peer_set):
                       /\ channels[self][remote_peer_index].header # defaultInitValue
                       /\ command' = [command EXCEPT ![self] = channels[self][remote_peer_index].header.command_name]
                       /\ IF command'[self] = "addr"
                             THEN /\ /\ local_peer_id_a' = [local_peer_id_a EXCEPT ![self] = self]
                                     /\ remote_peer_id_a' = [remote_peer_id_a EXCEPT ![self] = remote_peer_index]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addr",
                                                                              pc        |->  "Listening",
                                                                              local_peer_id_a |->  local_peer_id_a[self],
                                                                              remote_peer_id_a |->  remote_peer_id_a[self] ] >>
                                                                          \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "SendVersionMsg"]
                                  /\ UNCHANGED << local_peer_id_v, 
                                                  remote_peer_id_v, 
                                                  local_peer_id_ve, 
                                                  remote_peer_id_ve, 
                                                  local_peer_id_g, 
                                                  remote_peer_id_g, 
                                                  found_blocks, hash_count, 
                                                  block_header_hashes, 
                                                  remote_peer_blocks, 
                                                  start_height, end_height, 
                                                  local_peer_id_i, 
                                                  remote_peer_id_i, 
                                                  local_peer_id, 
                                                  remote_peer_id, blocks_data >>
                             ELSE /\ IF command'[self] = "version"
                                        THEN /\ /\ local_peer_id_v' = [local_peer_id_v EXCEPT ![self] = self]
                                                /\ remote_peer_id_v' = [remote_peer_id_v EXCEPT ![self] = remote_peer_index]
                                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "version",
                                                                                         pc        |->  "Listening",
                                                                                         local_peer_id_v |->  local_peer_id_v[self],
                                                                                         remote_peer_id_v |->  remote_peer_id_v[self] ] >>
                                                                                     \o stack[self]]
                                             /\ pc' = [pc EXCEPT ![self] = "HandleVersionMsg"]
                                             /\ UNCHANGED << local_peer_id_ve, 
                                                             remote_peer_id_ve, 
                                                             local_peer_id_g, 
                                                             remote_peer_id_g, 
                                                             found_blocks, 
                                                             hash_count, 
                                                             block_header_hashes, 
                                                             remote_peer_blocks, 
                                                             start_height, 
                                                             end_height, 
                                                             local_peer_id_i, 
                                                             remote_peer_id_i, 
                                                             local_peer_id, 
                                                             remote_peer_id, 
                                                             blocks_data >>
                                        ELSE /\ IF command'[self] = "verack"
                                                   THEN /\ /\ local_peer_id_ve' = [local_peer_id_ve EXCEPT ![self] = self]
                                                           /\ remote_peer_id_ve' = [remote_peer_id_ve EXCEPT ![self] = remote_peer_index]
                                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "verack",
                                                                                                    pc        |->  "ListenerLoop",
                                                                                                    local_peer_id_ve |->  local_peer_id_ve[self],
                                                                                                    remote_peer_id_ve |->  remote_peer_id_ve[self] ] >>
                                                                                                \o stack[self]]
                                                        /\ pc' = [pc EXCEPT ![self] = "HandleVerackMsg"]
                                                        /\ UNCHANGED << local_peer_id_g, 
                                                                        remote_peer_id_g, 
                                                                        found_blocks, 
                                                                        hash_count, 
                                                                        block_header_hashes, 
                                                                        remote_peer_blocks, 
                                                                        start_height, 
                                                                        end_height, 
                                                                        local_peer_id_i, 
                                                                        remote_peer_id_i, 
                                                                        local_peer_id, 
                                                                        remote_peer_id, 
                                                                        blocks_data >>
                                                   ELSE /\ IF command'[self] = "getblocks"
                                                              THEN /\ /\ local_peer_id_g' = [local_peer_id_g EXCEPT ![self] = self]
                                                                      /\ remote_peer_id_g' = [remote_peer_id_g EXCEPT ![self] = remote_peer_index]
                                                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getblocks",
                                                                                                               pc        |->  "Listening",
                                                                                                               found_blocks |->  found_blocks[self],
                                                                                                               hash_count |->  hash_count[self],
                                                                                                               block_header_hashes |->  block_header_hashes[self],
                                                                                                               remote_peer_blocks |->  remote_peer_blocks[self],
                                                                                                               start_height |->  start_height[self],
                                                                                                               end_height |->  end_height[self],
                                                                                                               local_peer_id_g |->  local_peer_id_g[self],
                                                                                                               remote_peer_id_g |->  remote_peer_id_g[self] ] >>
                                                                                                           \o stack[self]]
                                                                   /\ found_blocks' = [found_blocks EXCEPT ![self] = defaultInitValue]
                                                                   /\ hash_count' = [hash_count EXCEPT ![self] = defaultInitValue]
                                                                   /\ block_header_hashes' = [block_header_hashes EXCEPT ![self] = defaultInitValue]
                                                                   /\ remote_peer_blocks' = [remote_peer_blocks EXCEPT ![self] = defaultInitValue]
                                                                   /\ start_height' = [start_height EXCEPT ![self] = defaultInitValue]
                                                                   /\ end_height' = [end_height EXCEPT ![self] = defaultInitValue]
                                                                   /\ pc' = [pc EXCEPT ![self] = "HandleGetBlocksMsg"]
                                                                   /\ UNCHANGED << local_peer_id_i, 
                                                                                   remote_peer_id_i, 
                                                                                   local_peer_id, 
                                                                                   remote_peer_id, 
                                                                                   blocks_data >>
                                                              ELSE /\ IF command'[self] = "inv"
                                                                         THEN /\ /\ local_peer_id_i' = [local_peer_id_i EXCEPT ![self] = self]
                                                                                 /\ remote_peer_id_i' = [remote_peer_id_i EXCEPT ![self] = remote_peer_index]
                                                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "inv",
                                                                                                                          pc        |->  "Listening",
                                                                                                                          local_peer_id_i |->  local_peer_id_i[self],
                                                                                                                          remote_peer_id_i |->  remote_peer_id_i[self] ] >>
                                                                                                                      \o stack[self]]
                                                                              /\ pc' = [pc EXCEPT ![self] = "SendGetDataMsg"]
                                                                              /\ UNCHANGED << local_peer_id, 
                                                                                              remote_peer_id, 
                                                                                              blocks_data >>
                                                                         ELSE /\ IF command'[self] = "getdata"
                                                                                    THEN /\ /\ local_peer_id' = [local_peer_id EXCEPT ![self] = self]
                                                                                            /\ remote_peer_id' = [remote_peer_id EXCEPT ![self] = remote_peer_index]
                                                                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getdata",
                                                                                                                                     pc        |->  "ListenerLoop",
                                                                                                                                     blocks_data |->  blocks_data[self],
                                                                                                                                     local_peer_id |->  local_peer_id[self],
                                                                                                                                     remote_peer_id |->  remote_peer_id[self] ] >>
                                                                                                                                 \o stack[self]]
                                                                                         /\ blocks_data' = [blocks_data EXCEPT ![self] = defaultInitValue]
                                                                                         /\ pc' = [pc EXCEPT ![self] = "Incorporate"]
                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "ListenerLoop"]
                                                                                         /\ UNCHANGED << stack, 
                                                                                                         local_peer_id, 
                                                                                                         remote_peer_id, 
                                                                                                         blocks_data >>
                                                                              /\ UNCHANGED << local_peer_id_i, 
                                                                                              remote_peer_id_i >>
                                                                   /\ UNCHANGED << local_peer_id_g, 
                                                                                   remote_peer_id_g, 
                                                                                   found_blocks, 
                                                                                   hash_count, 
                                                                                   block_header_hashes, 
                                                                                   remote_peer_blocks, 
                                                                                   start_height, 
                                                                                   end_height >>
                                                        /\ UNCHANGED << local_peer_id_ve, 
                                                                        remote_peer_id_ve >>
                                             /\ UNCHANGED << local_peer_id_v, 
                                                             remote_peer_id_v >>
                                  /\ UNCHANGED << local_peer_id_a, 
                                                  remote_peer_id_a >>
                  /\ UNCHANGED << the_network, channels, local_peer_id_, 
                                  remote_peer_id_, hashes, local_peer_id_r, 
                                  remote_peer_id_r, local_peer_index, best_tip >>

ListenerLoop(self) == /\ pc[self] = "ListenerLoop"
                      /\ \E remote_peer_index \in 1..Len(the_network[self].peer_set):
                           /\ channels' = [channels EXCEPT ![self][remote_peer_index] = [header |-> defaultInitValue, payload |-> defaultInitValue]]
                           /\ pc' = [pc EXCEPT ![self] = "Listening"]
                      /\ UNCHANGED << the_network, stack, local_peer_id_, 
                                      remote_peer_id_, local_peer_id_a, 
                                      remote_peer_id_a, local_peer_id_v, 
                                      remote_peer_id_v, local_peer_id_ve, 
                                      remote_peer_id_ve, local_peer_id_g, 
                                      remote_peer_id_g, found_blocks, 
                                      hash_count, block_header_hashes, 
                                      remote_peer_blocks, start_height, 
                                      end_height, hashes, local_peer_id_r, 
                                      remote_peer_id_r, local_peer_id_i, 
                                      remote_peer_id_i, local_peer_id, 
                                      remote_peer_id, blocks_data, command, 
                                      local_peer_index, best_tip >>

LISTENER(self) == Listening(self) \/ Requests(self) \/ ListenerLoop(self)

Announce(self) == /\ pc[self] = "Announce"
                  /\ Assert(Len(the_network) >= 2, 
                            "Failure of assertion at line 224, column 9.")
                  /\ Len(the_network[local_peer_index[self]].peer_set) > 0
                  /\ \E remote_peer_index \in 1..Len(the_network[local_peer_index[self]].peer_set):
                       /\ /\ local_peer_id_' = [local_peer_id_ EXCEPT ![self] = local_peer_index[self]]
                          /\ remote_peer_id_' = [remote_peer_id_ EXCEPT ![self] = remote_peer_index]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "announce",
                                                                   pc        |->  "RequestInventory",
                                                                   local_peer_id_ |->  local_peer_id_[self],
                                                                   remote_peer_id_ |->  remote_peer_id_[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "SendAddrMsg"]
                  /\ UNCHANGED << the_network, channels, local_peer_id_a, 
                                  remote_peer_id_a, local_peer_id_v, 
                                  remote_peer_id_v, local_peer_id_ve, 
                                  remote_peer_id_ve, local_peer_id_g, 
                                  remote_peer_id_g, found_blocks, hash_count, 
                                  block_header_hashes, remote_peer_blocks, 
                                  start_height, end_height, hashes, 
                                  local_peer_id_r, remote_peer_id_r, 
                                  local_peer_id_i, remote_peer_id_i, 
                                  local_peer_id, remote_peer_id, blocks_data, 
                                  command, local_peer_index, best_tip >>

RequestInventory(self) == /\ pc[self] = "RequestInventory"
                          /\ \E remote_peer_index \in 1..Len(the_network[local_peer_index[self]].peer_set):
                               /\ the_network[local_peer_index[self]].peer_set[remote_peer_index].established = TRUE
                               /\ IF the_network[local_peer_index[self]].peer_set[remote_peer_index].tip > best_tip[self]
                                     THEN /\ best_tip' = [best_tip EXCEPT ![self] = the_network[local_peer_index[self]].peer_set[remote_peer_index].tip]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED best_tip
                               /\   channels[local_peer_index[self]][remote_peer_index].header = defaultInitValue
                                  /\ channels[local_peer_index[self]][remote_peer_index].payload = defaultInitValue
                               /\ IF the_network[local_peer_index[self]].chain_tip.height <
                                      the_network[local_peer_index[self]].peer_set[remote_peer_index].tip
                                     THEN /\ IF the_network[local_peer_index[self]].chain_tip.height = 0
                                                THEN /\ /\ hashes' = [hashes EXCEPT ![self] = <<>>]
                                                        /\ local_peer_id_r' = [local_peer_id_r EXCEPT ![self] = local_peer_index[self]]
                                                        /\ remote_peer_id_r' = [remote_peer_id_r EXCEPT ![self] = remote_peer_index]
                                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                                 pc        |->  "CheckSync",
                                                                                                 hashes    |->  hashes[self],
                                                                                                 local_peer_id_r |->  local_peer_id_r[self],
                                                                                                 remote_peer_id_r |->  remote_peer_id_r[self] ] >>
                                                                                             \o stack[self]]
                                                     /\ pc' = [pc EXCEPT ![self] = "SendGetBlocksMsg"]
                                                ELSE /\ /\ hashes' = [hashes EXCEPT ![self] = <<the_network[local_peer_index[self]].chain_tip.hash>>]
                                                        /\ local_peer_id_r' = [local_peer_id_r EXCEPT ![self] = local_peer_index[self]]
                                                        /\ remote_peer_id_r' = [remote_peer_id_r EXCEPT ![self] = remote_peer_index]
                                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "request_blocks",
                                                                                                 pc        |->  "CheckSync",
                                                                                                 hashes    |->  hashes[self],
                                                                                                 local_peer_id_r |->  local_peer_id_r[self],
                                                                                                 remote_peer_id_r |->  remote_peer_id_r[self] ] >>
                                                                                             \o stack[self]]
                                                     /\ pc' = [pc EXCEPT ![self] = "SendGetBlocksMsg"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "CheckSync"]
                                          /\ UNCHANGED << stack, hashes, 
                                                          local_peer_id_r, 
                                                          remote_peer_id_r >>
                          /\ UNCHANGED << the_network, channels, 
                                          local_peer_id_, remote_peer_id_, 
                                          local_peer_id_a, remote_peer_id_a, 
                                          local_peer_id_v, remote_peer_id_v, 
                                          local_peer_id_ve, remote_peer_id_ve, 
                                          local_peer_id_g, remote_peer_id_g, 
                                          found_blocks, hash_count, 
                                          block_header_hashes, 
                                          remote_peer_blocks, start_height, 
                                          end_height, local_peer_id_i, 
                                          remote_peer_id_i, local_peer_id, 
                                          remote_peer_id, blocks_data, command, 
                                          local_peer_index >>

CheckSync(self) == /\ pc[self] = "CheckSync"
                   /\ the_network[local_peer_index[self]].chain_tip.height > 0
                   /\ IF the_network[local_peer_index[self]].chain_tip.height < best_tip[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "RequestInventory"]
                         ELSE /\ \E remote_peer_index \in 1..Len(the_network[local_peer_index[self]].peer_set):
                                     the_network[local_peer_index[self]].peer_set[remote_peer_index].established = TRUE
                                   /\ channels[local_peer_index[self]][remote_peer_index].header = defaultInitValue
                                   /\ channels[local_peer_index[self]][remote_peer_index].payload = defaultInitValue
                              /\ PrintT("Peer is in sync!")
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << the_network, channels, stack, 
                                   local_peer_id_, remote_peer_id_, 
                                   local_peer_id_a, remote_peer_id_a, 
                                   local_peer_id_v, remote_peer_id_v, 
                                   local_peer_id_ve, remote_peer_id_ve, 
                                   local_peer_id_g, remote_peer_id_g, 
                                   found_blocks, hash_count, 
                                   block_header_hashes, remote_peer_blocks, 
                                   start_height, end_height, hashes, 
                                   local_peer_id_r, remote_peer_id_r, 
                                   local_peer_id_i, remote_peer_id_i, 
                                   local_peer_id, remote_peer_id, blocks_data, 
                                   command, local_peer_index, best_tip >>

SYNCHRONIZER(self) == Announce(self) \/ RequestInventory(self)
                         \/ CheckSync(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ announce(self) \/ addr(self)
                               \/ version(self) \/ verack(self)
                               \/ getblocks(self) \/ request_blocks(self)
                               \/ inv(self) \/ getdata(self))
           \/ (\E self \in 1 .. Len(RunningBlockchain): LISTENER(self))
           \/ (\E self \in PeerProcessDiffId + 1 .. PeerProcessDiffId + Len(RunningBlockchain): SYNCHRONIZER(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
