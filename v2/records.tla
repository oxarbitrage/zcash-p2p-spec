---- MODULE records ----
(*
Record constructors for the version 2 Zcash P2P protocol (draft ZIP,
zcash/zips#1344). Records are the units carried on the handshake stream
and on announcement streams; request/response formats follow in later phases.

Fields that are irrelevant to the properties being verified (nonce, services,
user agent, relay preferences) are set to constant values to keep the TLC
state space manageable, following the same convention as the legacy
messages.tla.
*)

EXTENDS Naturals

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

====
