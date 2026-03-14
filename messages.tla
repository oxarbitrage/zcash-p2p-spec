---- MODULE messages ----
(*
    Message constructors for the Zcash P2P wire protocol (ZIP-0204).

    Each operator builds a record with a header (magic number, command name)
    and a payload whose fields mirror the on-wire format. Fields that are
    irrelevant to the properties being verified are set to constant values
    to keep the TLC state space manageable.
*)
EXTENDS Naturals, FiniteSets

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
