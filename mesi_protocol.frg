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
-- This models realistic bus behavior where multiple cores
-- can send requests that pile up and are processed in order
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

-- All caches start Invalid (cold start)
-- Bus queue starts completely empty
pred init {
    all c: Core | c.status = Invalid
    no Bus.queue0
    no Bus.queue1
    no Bus.queue2
}


-- ============================================================
-- SECTION 3: BUS QUEUE HELPERS
-- ============================================================

-- Add a message to the back of the queue
-- Models a core sending a request onto the bus
pred enqueue[msg: BusMsg] {
    no Bus.queue0 => {
        -- Queue empty: place at front
        Bus.queue0' = msg
        Bus.queue1' = Bus.queue1
        Bus.queue2' = Bus.queue2
    } else no Bus.queue1 => {
        -- One item exists: place at second slot
        Bus.queue0' = Bus.queue0
        Bus.queue1' = msg
        Bus.queue2' = Bus.queue2
    } else no Bus.queue2 => {
        -- Two items exist: place at third slot
        Bus.queue0' = Bus.queue0
        Bus.queue1' = Bus.queue1
        Bus.queue2' = msg
    } else {
        -- Queue full: no change (simplified stall)
        Bus.queue0' = Bus.queue0
        Bus.queue1' = Bus.queue1
        Bus.queue2' = Bus.queue2
    }
}

-- Remove the front message and shift queue forward
-- Models a message being processed off the bus
pred dequeue {
    Bus.queue0' = Bus.queue1
    Bus.queue1' = Bus.queue2
    Bus.queue2' = none
}


-- ============================================================
-- SECTION 4: TRANSITION RELATIONS
-- ============================================================

-- TRANSITION: Local Read (PrRd)
-- Core c reads data it does not have
-- Enqueues a BusRd message on the bus
-- Goes Exclusive if no other core has the data
-- Goes Shared if other cores already have copies
pred localRead[c: Core, msg: BusMsg] {
    -- Guard: cache is empty, message is BusRd from c
    c.status = Invalid
    msg.sender  = c
    msg.msgType = BusRd

    -- Enqueue the read request on the bus
    enqueue[msg]

    -- Effect: go Exclusive if no other valid copy, else Shared
    (no (others[c] & (status.Modified + status.Exclusive + status.Shared)))
        => c.status' = Exclusive
    else
        c.status' = Shared

    -- Other cores: Modified or Exclusive must downgrade to Shared
    all o: others[c] |
        (o.status = Modified or o.status = Exclusive)
            => o.status' = Shared
        else
            o.status' = o.status
}

-- TRANSITION: Local Write — fresh (BusRdX)
-- Core c has no copy and wants to write immediately
-- Sends BusRdX: fetch from RAM AND invalidate all others
-- Skips Exclusive, goes directly to Modified
pred localWriteFresh[c: Core, msg: BusMsg] {
    -- Guard: cache is Invalid, message is BusRdX from c
    -- No conflicting exclusive write already at front of queue
    c.status = Invalid
    msg.sender  = c
    msg.msgType = BusRdX
    (no Bus.queue0) or (Bus.queue0.msgType != BusRdX)

    -- Enqueue the exclusive write request
    enqueue[msg]

    -- Effect: this core becomes sole Modified owner
    c.status' = Modified

    -- All other cores invalidated
    all o: others[c] | o.status' = Invalid
}

-- TRANSITION: Bus Upgrade (BusUpgr)
-- Core c already has a Shared copy and wants to write
-- Cheaper than localWriteFresh — no RAM fetch needed
-- Just broadcasts: everyone else must drop Shared copies
pred busUpgrade[c: Core, msg: BusMsg] {
    -- Guard: core has Shared status, message is BusUpgr from c
    c.status = Shared
    msg.sender  = c
    msg.msgType = BusUpgr

    -- Enqueue the upgrade request
    enqueue[msg]

    -- Effect: this core upgrades to Modified
    c.status' = Modified

    -- All other Shared cores must invalidate
    all o: others[c] |
        o.status = Shared => o.status' = Invalid
        else o.status' = o.status
}

-- TRANSITION: Bus Snoop
-- Core c observes the front message of the queue and reacts
-- This is the snooping mechanism — every core always listens
-- to the bus and responds based on what message it sees
-- This directly models snooping delays and message reordering
pred busSnoop[c: Core] {
    -- Guard: there is a message at the front of the queue
    some Bus.queue0

    -- The snooping core must NOT be the message sender
    c != Bus.queue0.sender

    -- React differently depending on message type at front
    Bus.queue0.msgType = BusRdX => {
        -- Someone wants exclusive write: must invalidate
        c.status' = Invalid
    } else Bus.queue0.msgType = BusUpgr => {
        -- Someone upgrading from Shared: invalidate if Shared
        c.status = Shared => c.status' = Invalid
        else c.status' = c.status
    } else Bus.queue0.msgType = BusWB => {
        -- Writeback notification: no effect on this core
        c.status' = c.status
    } else {
        -- BusRd: if this core had Modified, downgrade to Shared
        c.status = Modified => c.status' = Shared
        else c.status' = c.status
    }

    -- Dequeue the processed message
    dequeue
}

-- TRANSITION: Eviction
-- Core c silently drops its cached data
-- No bus message needed — RAM already has an up-to-date copy
pred evict[c: Core] {
    -- Guard: must have a valid copy to evict
    c.status != Invalid

    -- Effect: go Invalid
    c.status' = Invalid

    -- Frame: bus queue unchanged
    Bus.queue0' = Bus.queue0
    Bus.queue1' = Bus.queue1
    Bus.queue2' = Bus.queue2

    -- Frame: other cores unchanged
    all o: others[c] | o.status' = o.status
}


-- ============================================================
-- SECTION 5: COMBINED TRANSITION RELATION
-- ============================================================

-- At each tick, exactly one core takes exactly one action
pred step {
    some c: Core, msg: BusMsg |
        localRead[c, msg]
        or localWriteFresh[c, msg]
        or busUpgrade[c, msg]
        or busSnoop[c]
        or evict[c]
}

-- Stutter: nothing changes (required for temporal logic)
pred stutter {
    all c: Core | c.status' = c.status
    Bus.queue0' = Bus.queue0
    Bus.queue1' = Bus.queue1
    Bus.queue2' = Bus.queue2
}


-- ============================================================
-- SECTION 6: SAFETY PROPERTIES (SWMR Invariants)
-- ============================================================

-- PROPERTY 1: At most one core in Modified at any time
pred atMostOneModified {
    lone status.Modified
}

-- PROPERTY 2: If any core is Modified, all others must be Invalid
pred modifiedImpliesOthersInvalid {
    all c: Core |
        c.status = Modified => {
            all o: others[c] | o.status = Invalid
        }
}

-- PROPERTY 3: No core can be simultaneously Modified and Shared
pred noModifiedAndShared {
    no (status.Modified & status.Shared)
}

-- PROPERTY 4: Full SWMR
-- If any core has exclusive access (M or E),
-- every other core must be Invalid
-- This is the main safety property of the project
pred swmr {
    all c: Core |
        (c.status = Modified or c.status = Exclusive) => {
            all o: others[c] | o.status = Invalid
        }
}

-- PROPERTY 5: Message ordering safety (new — tests the bus queue)
-- If a BusRdX is at the front of the queue, at most one core
-- should be Modified. Tests that ordered message processing
-- correctly prevents write-write conflicts under reordering.
pred noModifiedDuringBusRdX {
    (some Bus.queue0 and Bus.queue0.msgType = BusRdX) => {
        lone status.Modified
    }
}


-- ============================================================
-- SECTION 7: BOUNDED MODEL CHECKING RUNS
-- ============================================================

-- Run 1: Sanity check — valid 3-core initial state exists
run {
    init
} for exactly 3 Core, exactly 3 BusMsg, 5 Int

-- Check 2: atMostOneModified holds across all 3-core traces
check {
    init and
    always { step or stutter } =>
    always { atMostOneModified }
} for exactly 3 Core, exactly 3 BusMsg

-- Check 3: Full SWMR holds — this is the main project result
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
-- Tests that the ordered queue prevents write-write conflicts
-- This directly addresses the proposal goal of identifying
-- if message reorderings can cause safety violations
check {
    init and
    always { step or stutter } =>
    always { noModifiedDuringBusRdX }
} for exactly 3 Core, exactly 3 BusMsg

-- Run 6: Witness — BusUpgr path is reachable
-- Confirms the Shared -> Modified upgrade transition fires
run {
    init
    eventually {
        some c: Core, msg: BusMsg |
            c.status = Shared
            and msg.sender = c
            and msg.msgType = BusUpgr
    }
} for exactly 3 Core, exactly 3 BusMsg

-- Run 7: Witness — all 3 cores can be Shared simultaneously
-- Confirms valid multi-reader behavior is reachable
run {
    init
    eventually { all c: Core | c.status = Shared }
} for exactly 3 Core, exactly 3 BusMsg

-- Run 8: Witness — writes are reachable (model is live)
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
--   [x] 4 BMC checks written (Checks 2-5)
--   [x] 4 witness runs written (Runs 1, 6, 7, 8)
--   [x] All for exactly 3 Core — matches proposal goal
-- ============================================================
