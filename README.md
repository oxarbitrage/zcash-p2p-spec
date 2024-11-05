# The Zcash P2P Protocol Specification

The Zcash P2P protocol is a decentralized system, inherited as a subset from the [Bitcoin P2P protocol](https://developer.bitcoin.org/reference/p2p_networking.html). The primary role of this protocol is to keep nodes synchronized with the network. Peers exchange a set of well-defined messages, but the synchronization algorithm is not standardized, allowing for variation in implementations.

This specification describes an approach where peers can connect to multiple other peers, aiming to load balance the workload and download blocks in parallel.

## Motivation

Specifications are typically written to identify and fix bugs, justifying the effort involved. However, the primary motivations for this project are:

- To learn more PlusCal and TLA+.
- To formally define a blockchain synchronization algorithm.
- To prove properties (liveness, safety, etc) of the resulting algorithm.

This is an ongoing project, and comments or contributions are highly encouraged.

## Project Structure

The project consists of several files, with `p2p.tla` being the core specification. The distriubted algorithm is implemented in PlusCal while additional files are pure TLA+.

- [Spec](p2p.tla)
- [PDF's](documents/)
- [Blockchain](Blockchain.tla)
- [Operators](Operators.tla)
- [Utils](Utils.tla)

## Model Overview

The model operates based on initial network conditions defined in the `Blockchain.tla` module. Variables such as the number of peers, the blocks each peer holds, and the peer set of each peer influence the model's state and behavior during model checking with TLC.

### Running the Model

To run the model, we use the [TLA+ for Visual Studio Code](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) extension, which parses the PlusCal code into TLA+ and allows us to run the TLC model checker.

The Blockchain.tla module includes different initial conditions, labeled as `Blockchain1`, `Blockchain2`, etc.

In `p2p.cfg` assign the desired conditions, for example:

```
RunningBlockchain <- Blockchain7
```

Then, run the TLC model checker against the parsed `p2p.tla` file.

## Internals

The algorithm consists of two processes running in parallel.

### LISTENER process

This process listens for incoming messages and calls the corresponding procedure when a message arrives on the channel established between two connected peers. The following are the supported messages in this specification:

```mermaid
flowchart TD
LISTENER[[LISTENER]] --> |Listen|addr
LISTENER --> |Listen|version
LISTENER --> |Listen|verack
LISTENER --> |Listen|getblocks
LISTENER --> |Listen|inv
LISTENER --> |Listen|getdata
```

### SYNCHRONIZER process

This process manages connections between peers. Connections are created between each peer listed in the `RunningBlockchain` sequence and their respective peers in the `peer_set`. Once connected, peers will request blocks and attempt to synchronize with the network.

The following diagram assumes a network of three peers (peer1, peer2, and peer3), where peer2 has peer1 and peer3 in its peer_set.

`SYNCHRONIZER` will not open connections for peer1 and peer3 since they have no peers in their `peer_set`. For peer2, connections with peer1 and peer3 will be established, and blocks will be requested from both until peer2 is in sync, at which point the algorithm terminates.

```mermaid
flowchart TD
SYNCHRONIZER[[SYNCHRONIZER]] --> |For peer2|announce
announce --> |Connect|peer1
announce --> |Connect|peer3
sync --> |Request blocks|peer1
peer1 --> |Send blocks|sync
sync --> |Request blocks|peer3
peer3 --> |Send blocks|sync
sync ---> |Peer in sync|terminate
```

### Single Peer Synchronization

Let's now consider a network with just two peers (peer1 and peer2), where peer1 is in the `peer_set` of peer2 and has blocks. The following diagram shows how the `SYNCHRONIZER` and `LISTENER` processes interact to synchronize peer2 with the rest of the network (peer1) at the message level.

```mermaid
flowchart TD
LISTENER[[LISTENER]] --> |Listen|addr
LISTENER --> |Listen|version
LISTENER --> |Listen|verack
LISTENER --> |Listen|getblocks
LISTENER --> |Listen|inv
LISTENER --> |Listen|getdata

SYNCHRONIZER[[SYNCHRONIZER]] --> |For peer2|announce
announce --> |Start Connecting|send_addr_msg([SendAddrMsg])
send_addr_msg --> |Process|addr
addr --> |Start Hansdhake|send_version_msg([SendVersionMsg])
send_version_msg --> |Process|version
version --> |More Hanshake|send_verack_msg([SendVerackMsg])
send_verack_msg --> |End Handshake - Connected|verack

announce --> |Await connected|sync
sync --> |Decide blocks to be requested|request_blocks
request_blocks --> |Request inv|send_getblocks_msg([SendGetBlocksMsg])
send_getblocks_msg --> |Process|getblocks
getblocks --> |Get inv|send_inv_msg([SendInvMsg])
send_inv_msg --> |Process|inv
inv --> |Request data|send_getdata_msg([SendGetDataMsg])
send_getdata_msg --> |Process|getdata
getdata --> |Add data to peer|incorporate
incorporate --> |Sync loop|sync
incorporate --> |End algorithm|terminate
```

### Load balancing

In a network with three peers (peer1, peer2, and peer3), where only peer2 has peers in its `peer_set` (specifically, peer1 and peer3), the following sequence occurs:

After connecting with both peers, the `SYNCHRONIZER` requests a batch of blocks from peer1. If this batch is insufficient for full synchronization, another batch is requested from peer3, and the process repeats until peer2 is fully synchronized.
 
```mermaid
sequenceDiagram
    Peer2->>Peer1: Request blocks
    Peer1->>Peer2: Send blocks

    Peer2->>Peer2: Need more blocks? YES
    Peer2->>Peer3: Request more blocks
    Peer3 ->>Peer2: Send more blocks

    Peer2->>Peer2: Need more blocks? YES

    Peer2->>Peer1: Request more blocks
    Peer1->>Peer2: Send more blocks

    Peer2->>Peer2: Need more blocks? NO
```
