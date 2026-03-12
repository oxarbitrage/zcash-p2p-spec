---- MODULE messages ----
EXTENDS Naturals, FiniteSets

\* Timestamps are omitted from message constructors: no action or invariant reads them,
\* and including clock-varying values would unnecessarily inflate the TLC state space.

MakeVersion(from, to, blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "version" ],
    payload |-> [
        version      |-> 170100,
        services     |-> 0,
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

MakePing == [
    header  |-> [ magic |-> 619259748, command |-> "ping" ],
    payload |-> [ nonce |-> 0 ]
]

MakePong == [
    header  |-> [ magic |-> 619259748, command |-> "pong" ],
    payload |-> [ nonce |-> 0 ]
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
        version            |-> 170100,
        hashCount          |-> 1,
        blockLocatorHashes |-> << Cardinality(blocks) >>,
        hashStop           |-> 0
    ]
]

MakeHeaders(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "headers" ],
    payload |-> [
        count   |-> 1,
        headers |-> << [ version |-> 170140, prev_block |-> Cardinality(blocks), merkle_root |-> 0, bits |-> 0, nonce |-> 0 ] >>
    ]
]

MakeGetData(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "getdata" ],
    payload |-> [
        count     |-> 1,
        inventory |-> << [ type |-> "MSG_BLOCK", hash |-> Cardinality(blocks) ] >>
    ]
]

MakeReject(rejected_command) == [
    header  |-> [ magic |-> 619259748, command |-> "reject" ],
    payload |-> [ message |-> rejected_command ]
]

MakeBlock(blocks) == [
    header  |-> [ magic |-> 619259748, command |-> "block" ],
    payload |-> [
        version      |-> 70015,
        prev_block   |-> Cardinality(blocks),
        merkle_root  |-> 0,
        bits         |-> 0,
        nonce        |-> 0,
        transactions |-> << >>
    ]
]

====
