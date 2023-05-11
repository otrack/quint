// -*- mode: Bluespec; -*-
module System{
    type Process = str
    type Tx = str

    pure val PROCESSES = Set("alice", "bob", "charlie")
    pure val TXS = Set("t0", "t1", "t2")
}
