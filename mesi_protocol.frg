#lang forge
option problem_type temporal
option max_tracelength 7


abstract sig CacheState {}
one sig Modified, Exclusive, Shared, Invalid extends CacheState {}

abstract sig MsgType {}
one sig BusRd   extends MsgType {}
one sig BusRdX  extends MsgType {}
one sig BusUpgr extends MsgType {}
one sig BusWB   extends MsgType {}

sig BusMsg {
    sender  : one Core,
    msgType : one MsgType
}

sig Core {
    var status: one CacheState
}

one sig Bus {
    var queue0 : lone BusMsg,
    var queue1 : lone BusMsg,
    var queue2 : lone BusMsg
}

fun others[c: Core]: set Core { Core - c }


-- INITIAL STATE

pred init {
    all c: Core | c.status = Invalid
    no Bus.queue0
    no Bus.queue1
    no Bus.queue2
}


-- BUS QUEUE HELPERS

pred enqueue[msg: BusMsg] {
    no Bus.queue0 => {
        Bus.queue0' = msg
        Bus.queue1' = Bus.queue1
        Bus.queue2' = Bus.queue2
    } else no Bus.queue1 => {
        Bus.queue0' = Bus.queue0
        Bus.queue1' = msg
        Bus.queue2' = Bus.queue2
    } else no Bus.queue2 => {
        Bus.queue0' = Bus.queue0
        Bus.queue1' = Bus.queue1
        Bus.queue2' = msg
    } else {
        Bus.queue0' = Bus.queue0
        Bus.queue1' = Bus.queue1
        Bus.queue2' = Bus.queue2
    }
}

pred dequeue {
    Bus.queue0' = Bus.queue1
    Bus.queue1' = Bus.queue2
    Bus.queue2' = none
}


-- TRANSITION RELATIONS

-- TRANSITION: Local Read (PrRd)
pred localRead[c: Core, msg: BusMsg] {
    -- Guard
    c.status = Invalid
    msg.sender  = c
    msg.msgType = BusRd

    -- Enqueue
    enqueue[msg]

    -- Effect on reading core
    (no (others[c] & (status.Modified + status.Exclusive + status.Shared)))
        => c.status' = Exclusive
    else
        c.status' = Shared

    -- Effect on ALL other cores — complete frame
    all o: others[c] | {
        (o.status = Modified or o.status = Exclusive)
            => o.status' = Shared
        else
            o.status' = o.status
    }
}

-- TRANSITION: Local Write fresh (BusRdX)
pred localWriteFresh[c: Core, msg: BusMsg] {
    -- Guard
    c.status = Invalid
    msg.sender  = c
    msg.msgType = BusRdX
    (no Bus.queue0) or (Bus.queue0.msgType != BusRdX)

    -- Enqueue
    enqueue[msg]

    -- Effect: writing core goes Modified
    c.status' = Modified

    -- Effect: ALL other cores go Invalid — complete frame
    all o: others[c] | o.status' = Invalid
}

-- TRANSITION: Bus Upgrade (BusUpgr)
pred busUpgrade[c: Core, msg: BusMsg] {
    -- Guard: must be Shared, no other core Modified or Exclusive
    c.status = Shared
    msg.sender  = c
    msg.msgType = BusUpgr
    no (others[c] & (status.Modified + status.Exclusive))

    -- Enqueue
    enqueue[msg]

    -- Effect: upgrading core goes Modified
    c.status' = Modified

    -- Effect on ALL other cores — complete frame
    all o: others[c] | {
        (o.status = Shared or o.status = Exclusive)
            => o.status' = Invalid
        else
            o.status' = o.status
    }
}

-- TRANSITION: Bus Snoop
pred busSnoop[c: Core] {
    -- Guard
    some Bus.queue0
    c != Bus.queue0.sender

    -- Effect on snooping core based on message type
    Bus.queue0.msgType = BusRdX => {
        c.status' = Invalid
    } else Bus.queue0.msgType = BusUpgr => {
        c.status = Shared => c.status' = Invalid
        else c.status' = c.status
    } else Bus.queue0.msgType = BusWB => {
        c.status' = c.status
    } else {
        -- BusRd
        c.status = Modified => c.status' = Shared
        else c.status' = c.status
    }

    -- Frame: ALL other cores not involved stay the same
    all o: Core | {
        (o != c and o != Bus.queue0.sender) =>
            o.status' = o.status
    }

    -- Frame: sender status unchanged during snoop
    Bus.queue0.sender.status' = Bus.queue0.sender.status

    -- Dequeue
    dequeue
}

-- TRANSITION: Eviction
pred evict[c: Core] {
    -- Guard
    c.status != Invalid

    -- Effect
    c.status' = Invalid

    -- Frame: bus queue unchanged
    Bus.queue0' = Bus.queue0
    Bus.queue1' = Bus.queue1
    Bus.queue2' = Bus.queue2

    -- Frame: ALL other cores unchanged
    all o: others[c] | o.status' = o.status
}


-- COMBINED TRANSITION RELATION

pred step {
    some c: Core, msg: BusMsg |
        localRead[c, msg]
        or localWriteFresh[c, msg]
        or busUpgrade[c, msg]
        or busSnoop[c]
        or evict[c]
}

pred stutter {
    all c: Core | c.status' = c.status
    Bus.queue0' = Bus.queue0
    Bus.queue1' = Bus.queue1
    Bus.queue2' = Bus.queue2
}


-- SAFETY PROPERTIES

pred atMostOneModified {
    lone status.Modified
}

pred modifiedImpliesOthersInvalid {
    all c: Core |
        c.status = Modified => {
            all o: others[c] | o.status = Invalid
        }
}

pred noModifiedAndShared {
    no (status.Modified & status.Shared)
}

pred swmr {
    all c: Core |
        (c.status = Modified or c.status = Exclusive) => {
            all o: others[c] | o.status = Invalid
        }
}

pred noModifiedDuringBusRdX {
    some Bus.queue0 and Bus.queue0.msgType = BusRdX => {
        lone status.Modified
    }
}


-- BOUNDED MODEL CHECKING RUNS

run {
    init
} for exactly 3 Core, exactly 3 BusMsg, 5 Int

check {
    init and
    always { step or stutter } =>
    always { atMostOneModified }
} for exactly 3 Core, exactly 3 BusMsg

check {
    init and
    always { step or stutter } =>
    always { swmr }
} for exactly 3 Core, exactly 3 BusMsg

check {
    init and
    always { step or stutter } =>
    always { noModifiedAndShared }
} for exactly 3 Core, exactly 3 BusMsg

check {
    init and
    always { step or stutter } =>
    always { noModifiedDuringBusRdX }
} for exactly 3 Core, exactly 3 BusMsg

run {
    init
    eventually {
        some c: Core, msg: BusMsg |
            c.status = Shared
            and msg.sender = c
            and msg.msgType = BusUpgr
    }
} for exactly 3 Core, exactly 3 BusMsg

run {
    init
    eventually { all c: Core | c.status = Shared }
} for exactly 3 Core, exactly 3 BusMsg

run {
    init
    eventually { some c: Core | c.status = Modified }
} for exactly 3 Core, exactly 3 BusMsg