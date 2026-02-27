---- MODULE messages ----
EXTENDS Naturals, FiniteSets

MakeVersion(from, to, timestamp, blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "version", length |-> 0, checksum |-> 0 ],
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
    header |-> [ magic |-> 619259748, command |-> "verack", length |-> 0, checksum |-> 0 ]
]

MakePing == [
    header |-> [ magic |-> 619259748, command |-> "ping", length |-> 0, checksum |-> 0 ]
]

MakePong == [
    header |-> [ magic |-> 619259748, command |-> "pong", length |-> 0, checksum |-> 0 ]
]

MakeInv(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "inv", length |-> 0, checksum |-> 0 ],
    payload |-> [
        count     |-> 1,
        inventory |-> << [ type |-> "MSG_BLOCK", hash |-> Cardinality(blocks) ] >>
    ]
]

MakeGetHeaders(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "getheaders", length |-> 0, checksum |-> 0 ],
    payload |-> [
        version            |-> 70015,
        hashCount          |-> 1,
        blockLocatorHashes |-> << Cardinality(blocks) >>,
        hashStop           |-> 0
    ]
]

MakeHeaders(blocks, timestamp) == [
    header  |-> [ magic |-> 619259748, command |-> "headers", length |-> 0, checksum |-> 0 ],
    payload |-> [
        count   |-> 1,
        headers |-> << [ version |-> 70015, prev_block |-> Cardinality(blocks), merkle_root |-> 0, timestamp |-> timestamp, bits |-> 0, nonce |-> 0 ] >>
    ]
]

MakeGetData(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "getdata", length |-> 0, checksum |-> 0 ],
    payload |-> [
        count     |-> 1,
        inventory |-> << [ type |-> "MSG_BLOCK", hash |-> Cardinality(blocks) ] >>
    ]
]

MakeBlock(blocks, timestamp) == [
    header  |-> [ magic |-> 619259748, command |-> "block", length |-> 0, checksum |-> 0 ],
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
