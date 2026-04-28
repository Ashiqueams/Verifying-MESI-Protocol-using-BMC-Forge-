#lang forge
option problem_type temporal
option max_tracelength 7

-- ============================================================
-- Bounded Model Checking of a Simplified MESI Cache
-- Coherence Protocol in Forge
-- Ashique & Muntaha | CS 6110 Software Verification
-- ============================================================
--
-- GOAL: Produce a formal model of a 3-core MESI protocol
-- and verify that SWMR properties hold across all reachable
-- states within a specific bound. Identify if specific
-- snooping delays or message reorderings can cause a
-- violation of the safety properties.
-- ============================================================


-- ============================================================
-- SECTION 1: STATE SPACE DEFINITIONS
-- ============================================================

-- The four MESI cache line states
abstract sig CacheState {}
one sig Modified, Exclusive, Shared, Invalid extends CacheState {}

-- Message types that can appear on the bus
abstract sig MsgType {}
one sig BusRd   extends MsgType {} -- read request
one sig BusRdX  extends MsgType {} -- read with intent to modify
one sig BusUpgr extends MsgType {} -- upgrade Shared -> Modified
one sig BusWB   extends MsgType {} -- writeback Modified -> RAM

-- A bus message: who sent it and what kind it is
sig BusMsg {
    sender  : one Core,
    msgType : one MsgType
}

-- A core with a private cache
sig Core {
    var status: one CacheState
}

-- The shared memory bus with an ordered 3-slot message queue
-- queue0 = front (processed first, oldest request)
-- queue1 = middle
-- queue2 = back  (newest request, most recently enqueued)
one sig Bus {
    var queue0 : lone BusMsg,
    var queue1 : lone BusMsg,
    var queue2 : lone BusMsg
}

-- Helper: all cores OTHER than c
fun others[c: Core]: set Core { Core - c }


-- ============================================================
-- SECTION 2: INITIAL STATE
-- ============================================================

pred init {
    all c: Core | c.status = Invalid
    no Bus.queue0
    no Bus.queue1
    no Bus.queue2
}


-- ============================================================
-- SECTION 3: BUS QUEUE HELPERS
-- ============================================================

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


-- ============================================================
-- SECTION 4: TRANSITION RELATIONS
-- ============================================================

pred localRead[c: Core, msg: BusMsg] {
    c.status = Invalid
    msg.sender  = c
    msg.msgType = BusRd
    enqueue[msg]
    (no (others[c] & (status.Modified + status.Exclusive + status.Shared)))
        => c.status' = Exclusive
    else
        c.status' = Shared
    all o: others[c] |
        (o.status = Modified or o.status = Exclusive)
            => o.status' = Shared
        else
            o.status' = o.status
}

pred localWriteFresh[c: Core, msg: BusMsg] {
    c.status = Invalid
    msg.sender  = c
    msg.msgType = BusRdX
    (no Bus.queue0) or (Bus.queue0.msgType != BusRdX)
    enqueue[msg]
    c.status' = Modified
    all o: others[c] | o.status' = Invalid
}

pred busUpgrade[c: Core, msg: BusMsg] {
    c.status = Shared
    msg.sender  = c
    msg.msgType = BusUpgr

    no (others[c] & (status.Modified + status.Exclusive))

    enqueue[msg]
    c.status' = Modified

    all o: others[c] |
        o.status = Shared => o.status' = Invalid
        else o.status' = o.status
}

pred busSnoop[c: Core] {
    some Bus.queue0
    c != Bus.queue0.sender

    Bus.queue0.msgType = BusRdX => {
        c.status' = Invalid
    } else Bus.queue0.msgType = BusUpgr => {
        c.status = Shared => c.status' = Invalid
        else c.status' = c.status
    } else Bus.queue0.msgType = BusWB => {
        c.status' = c.status
    } else {
        c.status = Modified => c.status' = Shared
        else c.status' = c.status
    }

    all o: Core |
        (o != c and o != Bus.queue0.sender) =>
            o.status' = o.status

    dequeue
}

pred evict[c: Core] {
    c.status != Invalid
    c.status' = Invalid
    Bus.queue0' = Bus.queue0
    Bus.queue1' = Bus.queue1
    Bus.queue2' = Bus.queue2
    all o: others[c] | o.status' = o.status
}


-- ============================================================
-- SECTION 5: COMBINED TRANSITION RELATION
-- ============================================================

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


-- ============================================================
-- SECTION 6: SAFETY PROPERTIES (SWMR Invariants)
-- ============================================================

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


-- ============================================================
-- SECTION 7: BOUNDED MODEL CHECKING RUNS
-- ============================================================

-- Run 1: Sanity check
run {
    init
} for exactly 3 Core, exactly 3 BusMsg, 5 Int

-- Check 2: atMostOneModified
check {
    init and
    always { step or stutter } =>
    always { atMostOneModified }
} for exactly 3 Core, exactly 3 BusMsg

-- Check 3: Full SWMR — main project result
check {
    init and
    always { step or stutter } =>
    always { swmr }
} for exactly 3 Core, exactly 3 BusMsg

-- Check 4: No Modified+Shared co-existence
check {
    init and
    always { step or stutter } =>
    always { noModifiedAndShared }
} for exactly 3 Core, exactly 3 BusMsg

-- Check 5: Message ordering safety
check {
    init and
    always { step or stutter } =>
    always { noModifiedDuringBusRdX }
} for exactly 3 Core, exactly 3 BusMsg

-- Run 6: Witness — BusUpgr path is reachable
run {
    init
    eventually {
        some c: Core, msg: BusMsg |
            c.status = Shared
            and msg.sender = c
            and msg.msgType = BusUpgr
    }
} for exactly 3 Core, exactly 3 BusMsg

-- Run 7: Witness — all 3 cores Shared simultaneously
run {
    init
    eventually { all c: Core | c.status = Shared }
} for exactly 3 Core, exactly 3 BusMsg

-- Run 8: Witness — writes are reachable
run {
    init
    eventually { some c: Core | c.status = Modified }
} for exactly 3 Core, exactly 3 BusMsg


-- ============================================================
-- PROJECT STATUS
-- ============================================================
--
-- COMPLETED:
--   [x] 4 MESI states defined as abstract sigs
--   [x] Core sig with mutable var status field
--   [x] BusMsg sig with sender + msgType fields
--   [x] MsgType: BusRd, BusRdX, BusUpgr, BusWB
--   [x] Bus with ordered 3-slot queue (queue0/queue1/queue2)
--   [x] enqueue / dequeue queue helpers
--   [x] localRead    : Invalid -> Exclusive or Shared
--   [x] localWriteFresh : Invalid -> Modified via BusRdX
--   [x] busUpgrade   : Shared -> Modified via BusUpgr
--   [x] busSnoop     : reacts to front of queue by msg type
--   [x] evict        : silent drop to Invalid
--   [x] 5 safety properties encoded as formal invariants
--   [x] 4 BMC checks (Checks 2-5)
--   [x] 4 witness runs (Runs 1, 6, 7, 8)
--   [x] All for exactly 3 Core — matches proposal goal
-- ============================================================
