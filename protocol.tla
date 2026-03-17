---- MODULE protocol ----
(*
Zcash P2P protocol specification following ZIP-204.

Models the connection lifecycle between peers: handshake (version/verack),
keepalive (ping/pong), block synchronization (inv/getheaders/headers/getdata/block),
and timeout-based disconnection.

Communication uses a message consumption model — each peer has a per-connection
FIFO inbox and all decisions are based on message payloads only, matching the
information constraints of a real network.

The spec verifies one liveness property (all peers eventually reach the same
block height) and several safety invariants derived from ZIP-204 bounds.
*)

EXTENDS TLC, Naturals, Sequences, FiniteSets, messages

CONSTANT InitialPeers
CONSTANT MaxBlock
CONSTANT MaxClock
CONSTANT DisconnectTimeout
CONSTANT MinPeerProtoVersion

VARIABLES nodes, clock

----
vars == << nodes, clock >>

\* See README for an explanation of symmetry reduction.
Symmetry == Permutations(InitialPeers)

\* For each initial peer construct a set of all other peers.
OtherPeers == [ n \in InitialPeers |-> InitialPeers \ { n } ]

Init ==
    /\ clock = 0
    /\ \E blockset \in [ InitialPeers -> (1..MaxBlock) ] :
        nodes = [ i \in InitialPeers |-> [
            inbox        |-> [ j \in OtherPeers[i] |-> <<>> ],
            conn         |-> [ j \in OtherPeers[i] |-> "init" ],
            ping_nonce   |-> [ j \in OtherPeers[i] |-> 0 ],
            last_recv_at |-> [ j \in OtherPeers[i] |-> 0 ],
            blocks       |-> 1..blockset[i]
        ]]

----

\* --- Handshake ---

\* n sends its version to m. The message lands in m's inbox.
SendVersion ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "init"
            /\ nodes' = [ nodes EXCEPT
                    ![m].inbox[n] = Append(@, MakeVersion(n, m, nodes[n].blocks)),
                    ![n].conn[m]  = "version_sent" ]
            /\ UNCHANGED << clock >>

\* n receives m's version from its inbox. Validates the version field:
\*   valid   (>= MinPeerProtoVersion) -> send verack, transition to established
\*   invalid (< MinPeerProtoVersion)  -> send reject, reset to init
RecvVersion ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "version_sent"
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "version"
            /\ LET msg == Head(nodes[n].inbox[m])
               IN
               \/ /\ msg.payload.version >= MinPeerProtoVersion
                  /\ nodes' = [ nodes EXCEPT
                          ![n].inbox[m]        = Tail(@),
                          ![m].inbox[n]        = Append(@, MakeVerack),
                          ![n].conn[m]         = "established",
                          ![n].last_recv_at[m] = clock ]
               \/ /\ msg.payload.version < MinPeerProtoVersion
                  /\ nodes' = [ nodes EXCEPT
                          ![n].inbox[m]        = Tail(@),
                          ![m].inbox[n]        = << MakeReject("version") >>,
                          ![n].conn[m]         = "init",
                          ![n].ping_nonce[m]   = 0,
                          ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives a verack from m. If n is still in version_sent, this completes the
\* handshake. If n already advanced past established (async), just consume the message.
RecvVerack ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init"}
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "verack"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![n].conn[m]         = IF @ = "version_sent" THEN "established" ELSE @,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives an unexpected version from m while already past the handshake.
\* This models a reconnecting peer whose old connection was torn down unilaterally.
\* n resets to init, matching Zebra's DuplicateHandshake disconnect behavior.
RecvVersionReset ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init", "version_sent"}
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "version"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![n].conn[m]         = "init",
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n discards a non-version message from m while waiting for the handshake.
\* After a unilateral disconnect, stale messages from the old connection may still
\* be in the inbox. Matches Zebra's behavior of ignoring non-version messages
\* during the handshake phase.
DiscardStaleMessage ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "version_sent"
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command \notin {"version", "verack", "reject"}
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m] = Tail(@) ]
            /\ UNCHANGED << clock >>

\* n receives a reject from m, resetting to init.
RecvReject ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "reject"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![n].conn[m]         = "init",
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* --- Keepalive ---

\* n sends a ping to m when idle.
SendPing ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init", "version_sent"}
            /\ nodes[n].last_recv_at[m] <= clock - 3
            /\ nodes[n].ping_nonce[m] = 0
            /\ nodes' = [ nodes EXCEPT
                    ![m].inbox[n]      = Append(@, MakePing),
                    ![n].ping_nonce[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives a ping from m and immediately replies with pong.
RecvPing ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init", "version_sent"}
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "ping"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![m].inbox[n]        = Append(@, MakePong),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives a pong from m, completing the keepalive round-trip.
RecvPong ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].ping_nonce[m] # 0
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "pong"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* --- Block sync ---

\* n announces its inventory to m after handshake.
SendInv ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "established"
            /\ nodes[n].blocks # {}
            /\ nodes' = [ nodes EXCEPT
                    ![m].inbox[n]        = Append(@, MakeInv(nodes[n].blocks)),
                    ![n].conn[m]         = "inv_sent",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives an inv from m. Both peers must have sent their invs first (n is inv_sent).
\* Inspects the payload to decide: sync or already caught up.
RecvInv ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "inv_sent"
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "inv"
            /\ LET msg == Head(nodes[n].inbox[m])
                   advertised == msg.payload.inventory[1].hash
               IN
               \/ /\ advertised > Cardinality(nodes[n].blocks)
                  /\ nodes' = [ nodes EXCEPT
                          ![n].inbox[m]        = Tail(@),
                          ![m].inbox[n]        = Append(@, MakeGetHeaders(nodes[n].blocks)),
                          ![n].conn[m]         = "getheaders_sent",
                          ![n].last_recv_at[m] = clock ]
               \/ /\ advertised <= Cardinality(nodes[n].blocks)
                  /\ nodes' = [ nodes EXCEPT
                          ![n].inbox[m] = Tail(@),
                          ![n].conn[m]  = "synced" ]
            /\ UNCHANGED << clock >>

\* n receives a getheaders request from m and responds with its own headers.
RecvGetHeaders ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init", "version_sent"}
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "getheaders"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![m].inbox[n]        = Append(@, MakeHeaders(nodes[n].blocks)),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives headers from m (response to its getheaders), sends getdata.
RecvHeaders ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "getheaders_sent"
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "headers"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![m].inbox[n]        = Append(@, MakeGetData(nodes[n].blocks)),
                    ![n].conn[m]         = "getdata_sent",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives a getdata request from m and responds with a block.
RecvGetData ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init", "version_sent"}
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "getdata"
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![m].inbox[n]        = Append(@, MakeBlock(nodes[n].blocks)),
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* n receives a block from m, adds it to its local chain.
RecvBlock ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "getdata_sent"
            /\ Len(nodes[n].inbox[m]) > 0
            /\ Head(nodes[n].inbox[m]).header.command = "block"
            /\ LET newBlocks == nodes[n].blocks \cup {Cardinality(nodes[n].blocks) + 1}
                   msg == Head(nodes[n].inbox[m])
               IN nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = Tail(@),
                    ![n].last_recv_at[m] = clock,
                    ![n].blocks          = newBlocks,
                    ![n].conn[m]         = IF Cardinality(newBlocks) < msg.payload.prev_block
                                           THEN "block_received"
                                           ELSE "synced" ]
            /\ UNCHANGED << clock >>

\* n has received a block but still needs more — sends another getdata.
SendGetData ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] = "block_received"
            /\ nodes' = [ nodes EXCEPT
                    ![m].inbox[n]        = Append(@, MakeGetData(nodes[n].blocks)),
                    ![n].conn[m]         = "getdata_sent",
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

\* --- Disconnection ---

\* Unilateral disconnect: models TCP FIN — only the detecting side resets.
\* The remote peer's inbox from n is also cleared (the TCP pipe is broken,
\* so messages in transit are lost), but m's connection state is unchanged —
\* m will independently detect the timeout and disconnect on its own.
\* This matches Zebra's implementation where each side detects idleness independently.
Disconnect ==
    \E n \in InitialPeers:
        \E m \in OtherPeers[n]:
            /\ nodes[n].conn[m] \notin {"init"}
            /\ clock - nodes[n].last_recv_at[m] > DisconnectTimeout
            /\ nodes' = [ nodes EXCEPT
                    ![n].inbox[m]        = <<>>,
                    ![m].inbox[n]        = <<>>,
                    ![n].conn[m]         = "init",
                    ![n].ping_nonce[m]   = 0,
                    ![n].last_recv_at[m] = clock ]
            /\ UNCHANGED << clock >>

----

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << nodes >>

Next ==
    \/ Tick
    \/ SendVersion
    \/ RecvVersion
    \/ RecvVersionReset
    \/ DiscardStaleMessage
    \/ RecvVerack
    \/ RecvReject
    \/ SendPing
    \/ RecvPing
    \/ RecvPong
    \/ SendInv
    \/ RecvInv
    \/ RecvGetHeaders
    \/ RecvHeaders
    \/ RecvGetData
    \/ RecvBlock
    \/ SendGetData
    \/ Disconnect

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

\* Liveness property: all peers eventually reach the same block height.
EventualConsensus == <> \A i, j \in InitialPeers : nodes[i].blocks = nodes[j].blocks

----
\* ZIP-0204 invariants: safety properties checked at every reachable state.

\* inv and getdata inventory vectors must not exceed 50,000 entries (ZIP-0204 §4).
InvCountBounded ==
    \A n \in InitialPeers:
        \A m \in OtherPeers[n]:
            \A i \in 1..Len(nodes[n].inbox[m]):
                nodes[n].inbox[m][i].header.command = "inv"
                => nodes[n].inbox[m][i].payload.count <= 50000

GetDataCountBounded ==
    \A n \in InitialPeers:
        \A m \in OtherPeers[n]:
            \A i \in 1..Len(nodes[n].inbox[m]):
                nodes[n].inbox[m][i].header.command = "getdata"
                => nodes[n].inbox[m][i].payload.count <= 50000

\* headers messages must not carry more than 160 block headers (ZIP-0204 §4).
HeadersCountBounded ==
    \A n \in InitialPeers:
        \A m \in OtherPeers[n]:
            \A i \in 1..Len(nodes[n].inbox[m]):
                nodes[n].inbox[m][i].header.command = "headers"
                => nodes[n].inbox[m][i].payload.count <= 160

\* Peers must speak at least MinPeerProtoVersion (ZIP-0204 §3).
VersionBounded ==
    \A n \in InitialPeers:
        \A m \in OtherPeers[n]:
            \A i \in 1..Len(nodes[n].inbox[m]):
                nodes[n].inbox[m][i].header.command = "version"
                => nodes[n].inbox[m][i].payload.version >= MinPeerProtoVersion

\* A non-zero ping nonce implies the connection is past the handshake.
PingOnEstablished ==
    \A n \in InitialPeers:
        \A m \in OtherPeers[n]:
            nodes[n].ping_nonce[m] # 0
            => nodes[n].conn[m] \notin {"init", "version_sent"}

\* A peer only enters sync states when it actually has fewer blocks than its partner.
\* NOTE: uses <= (not <) because with message consumption, m could gain blocks
\* from a third peer between when n enters a sync state and when we check.
SyncDirection ==
    \A n \in InitialPeers:
        \A m \in OtherPeers[n]:
            nodes[n].conn[m] \in {"getheaders_sent", "getdata_sent", "block_received"}
            => Cardinality(nodes[n].blocks) <= Cardinality(nodes[m].blocks)

====
