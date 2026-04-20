#lang forge
option problem_type temporal
option max_tracelength 5



-- The four MESI cache line states
abstract sig CacheState {}
one sig Modified, Exclusive, Shared, Invalid extends CacheState {}

-- A core with a private cache
sig Core {
    var status: one CacheState
}

-- The shared memory bus 
one sig Bus {
    var pendingWrite: lone Core,   
    var pendingRead:  lone Core   
}

-- All caches start Invalid 
pred init {
    all c: Core | c.status = Invalid
    no Bus.pendingWrite
    no Bus.pendingRead
}


-- Helper: all cores OTHER than c
fun others[c: Core]: set Core { Core - c }

-- TRANSITION: A core performs a local read; if Invalid status then may go Exclusive or Shared
pred localRead[c: Core] {
    c.status = Invalid

    (no (others[c] & (status.Modified + status.Exclusive + status.Shared)))
        => c.status' = Exclusive
    else
        c.status' = Shared

    Bus.pendingRead'  = c
    Bus.pendingWrite' = Bus.pendingWrite

    -- Other cores: if they had Modified or Exclusive, they must downgrade to Shared
    all o: others[c] |
        (o.status = Modified or o.status = Exclusive)
            => o.status' = Shared
        else
            o.status' = o.status
}

-- A core performs a local write; Any status will go Modified; all other copies invalidated 
pred localWrite[c: Core] {
    no Bus.pendingWrite

    c.status' = Modified

    all o: others[c] | o.status' = Invalid

    -- Bus signals a write (BusRdX + BusUpgr)
    Bus.pendingWrite' = c
    Bus.pendingRead'  = none
}

-- Bus snoop — a core observes a BusRdX from another core
pred busSnoop[c: Core, requester: Core] {
    Bus.pendingWrite = requester
    c != requester

    c.status = Modified => c.status' = Invalid
    else c.status' = c.status

    -- bus and requester status unchanged by this transition
    Bus.pendingWrite' = Bus.pendingWrite
    Bus.pendingRead'  = Bus.pendingRead
    requester.status'  = requester.status
}

-- Eviction — a core silently evicts its cache line
pred evict[c: Core] {
    c.status != Invalid

    c.status' = Invalid

    Bus.pendingWrite' = Bus.pendingWrite
    Bus.pendingRead'  = Bus.pendingRead
    all o: others[c] | o.status' = o.status
}


pred step {
    some c: Core |
        localRead[c]
        or localWrite[c]
        or evict[c]
        or (some r: Core | busSnoop[c, r])
}

-- Stutter step: nothing changes 
pred stutter {
    all c: Core  | c.status'          = c.status
    Bus.pendingWrite' = Bus.pendingWrite
    Bus.pendingRead'  = Bus.pendingRead
}

-- SAFETY PROPERTIES 

-- PROPERTY 1: At most one core may be in Modified status at any time
pred atMostOneModified {
    lone status.Modified
}

-- PROPERTY 2: If any core is in Modified status, all others must be Invalid
pred modifiedImpliesOthersInvalid {
    all c: Core |
        c.status = Modified =>{
            all o: others[c] | o.status = Invalid
            }
}

-- PROPERTY 3: No core may be simultaneously Modified and Shared
pred noModifiedAndShared {
    no (status.Modified & status.Shared)
}

-- PROPERTY 4 (SWMR):At most one WRITER (Modified/Exclusive) OR any number of READERS (Shared)
-- but never both at the same time across different cores
pred swmr {
    all c: Core |
        (c.status = Modified or c.status = Exclusive) =>{
            all o: others[c] | o.status = Invalid
        }
}