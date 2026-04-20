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