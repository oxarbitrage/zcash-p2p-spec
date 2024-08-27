# The Zcash p2p network


### The LISTEN process

This processs just listen for incoming messages and call a procedure when a message arraives to the channel.

```mermaid
flowchart TD
LISTEN[[LISTEN]] --> addr
LISTEN --> version
LISTEN --> verack
LISTEN --> getblocks
LISTEN --> inv
LISTEN --> getdata
```

### The SYNC process

This process creates connections between the local peer and a remote peer in the local peer set. After the connection is established, the local node start requesting blocks form the remote peer.

```mermaid
flowchart TD
SYNC[[SYNC]] --> announce
announce --> sync
sync --> sync
```

### The full system

Both processes are always running, the following flowchart show how the 2 interact with each other.

```mermaid
flowchart TD
LISTEN[[LISTEN]] --> addr
LISTEN --> version
LISTEN --> verack
LISTEN --> getblocks
LISTEN --> inv
LISTEN --> getdata

SYNC[[SYNC]] --> announce
announce --> send_addr_msg([SendAddrMsg])
send_addr_msg --> addr
addr --> send_version_msg([SendVersionMsg])
send_version_msg --> version
version --> send_verack_msg([SendVerackMsg])
send_verack_msg --> verack

announce --> sync
sync --> request_blocks
request_blocks --> send_getblocks_msg([SendGetBlocksMsg])
send_getblocks_msg --> getblocks
getblocks --> send_inv_msg([SendInvMsg])
send_inv_msg --> inv
inv --> send_getdata_msg([SendGetDataMsg])
send_getdata_msg --> getdata
getdata --> incorporate
incorporate --> sync
incorporate --> terminate
```
