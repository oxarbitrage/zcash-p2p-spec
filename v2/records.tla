---- MODULE records ----
(*
Record constructors for the version 2 Zcash P2P protocol (draft ZIP,
zcash/zips#1344): the init record of the handshake stream, announcement
records, and the request/response formats of the get-headers and get-blocks
request streams.

Blocks are abstracted to their height on a single linear chain, so a block
hash, a block header and a block locator are all just heights.

Fields that are irrelevant to the properties being verified (nonce, services,
user agent, relay preferences) are set to constant values to keep the TLC
state space manageable, following the same convention as the legacy
messages.tla.
*)

EXTENDS Naturals, Sequences

\* The init record exchanged on the handshake stream (draft: "Init Record").
\* `version` is the sender's advertised protocol version and `start_height`
\* its best block height; both are the only fields the model acts on.
MakeInit(version, height) == [
    kind         |-> "init",
    version      |-> version,
    services     |-> 0,
    nonce        |-> 0,
    user_agent   |-> "",
    start_height |-> height,
    relay        |-> 1,
    announce     |-> 0,
    full_ids     |-> 0
]

\* A header announcement record on the block announcement stream
\* (draft: "Block Announcements", kind 0x00). The header is abstracted to
\* the height it carries.
MakeHeaderAnnouncement(height) == [
    kind   |-> "header",
    height |-> height
]


\* get-headers request (draft: "get-headers"). The locator is the requester's
\* tip; hash_stop is zero (as many headers as possible); tx_ids is 0.
MakeGetHeaders(locator) == [
    kind          |-> "get-headers",
    locator_count |-> 1,
    locator       |-> locator,
    hash_stop     |-> 0,
    tx_ids        |-> 0
]

\* get-headers response: the headers, as a sequence of heights.
MakeHeaders(heights) == [
    kind    |-> "headers",
    count   |-> Len(heights),
    heights |-> heights
]

\* get-blocks request (draft: "get-blocks"): the block hashes wanted.
MakeGetBlocks(heights) == [
    kind    |-> "get-blocks",
    count   |-> Len(heights),
    heights |-> heights
]

\* get-blocks response: the blocks delivered, a prefix of the request in
\* request order (the responder may finish after any complete entry).
MakeBlocks(heights) == [
    kind    |-> "blocks",
    count   |-> Len(heights),
    heights |-> heights
]

====
