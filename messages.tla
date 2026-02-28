---- MODULE messages ----
EXTENDS Naturals, FiniteSets

MakeVersion(from, to, timestamp, blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "version" ],
    payload |-> [
        version      |-> 70015,
        services     |-> 0,
        timestamp    |-> timestamp,
        addr_recv    |-> to,
        addr_from    |-> from,
        nonce        |-> 0,
        user_agent   |-> "",
        start_height |-> Cardinality(blocks),
        relay        |-> FALSE
    ]
]

MakeVerack == [
    header |-> [ magic |-> 619259748, command |-> "verack" ]
]

MakePing(nonce) == [
    header  |-> [ magic |-> 619259748, command |-> "ping" ],
    payload |-> [ nonce |-> nonce ]
]

MakePong(nonce) == [
    header  |-> [ magic |-> 619259748, command |-> "pong" ],
    payload |-> [ nonce |-> nonce ]
]

MakeInv(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "inv" ],
    payload |-> [
        count     |-> 1,
        inventory |-> << [ type |-> "MSG_BLOCK", hash |-> Cardinality(blocks) ] >>
    ]
]

MakeGetHeaders(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "getheaders" ],
    payload |-> [
        version            |-> 70015,
        hashCount          |-> 1,
        blockLocatorHashes |-> << Cardinality(blocks) >>,
        hashStop           |-> 0
    ]
]

MakeHeaders(blocks, timestamp) == [
    header  |-> [ magic |-> 619259748, command |-> "headers" ],
    payload |-> [
        count   |-> 1,
        headers |-> << [ version |-> 170140, prev_block |-> Cardinality(blocks), merkle_root |-> 0, timestamp |-> timestamp, bits |-> 0, nonce |-> 0 ] >>
    ]
]

MakeGetData(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "getdata" ],
    payload |-> [
        count     |-> 1,
        inventory |-> << [ type |-> "MSG_BLOCK", hash |-> Cardinality(blocks) ] >>
    ]
]

MakeBlock(blocks, timestamp) == [
    header  |-> [ magic |-> 619259748, command |-> "block" ],
    payload |-> [
        version      |-> 70015,
        prev_block   |-> Cardinality(blocks),
        merkle_root  |-> 0,
        timestamp    |-> timestamp,
        bits         |-> 0,
        nonce        |-> 0,
        transactions |-> << >>
    ]
]

====
