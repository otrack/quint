// -*- mode: Bluespec; -*-

module ABCI {

    import System.* from "../Common/System"
    import Ledger.* from "../Ledger/Ledger"

    type ABCIState = {
      ledger: LedgerState
    }

    pure def newABCI(l: LedgerState): ABCIState = {
      ledger: l
    }

    pure def isValid(state: ABCIState, t: Tx): bool = {
      not(isCommitted(state.ledger, t))
    }

}

module Mempool {

    import Spells.* from "../Common/Spells"
    import System.* from "../Common/System"
    import Ledger.* from "../Ledger/Ledger"
    import ABCI.*

    type MempoolState = {
      pool: Process -> Set[Tx],
      abci: ABCIState
    }

    pure def txsAvailable(state: MempoolState, p: Process): Set[Tx] = {
      state.pool.get(p)
    }

    pure def poolSize(state: MempoolState, p: Process): int = {
      state.pool.get(p).size()
    }

    pure def reap(state: MempoolState, p: Process, max: int): Set[Tx] = {
      setSubsetOfAtMost(state.pool.get(p), max)
    }

    pure def poolOf(state: MempoolState, p: Process): Set[Tx] = {
      state.pool.get(p)
    }

    pure def newMemPool(P: Set[Process], app: ABCIState): MempoolState = {
      pool: P.mapBy(p => Set()),
      abci: app
    }

    pure def add(state: MempoolState, p: Process, t: Tx): MempoolState = { // aka. checkTx
      state.with("pool", state.pool.set(p, state.pool.get(p).union(Set(t))))
    }

    pure def clear(state: MempoolState, p: Process): MempoolState = {
      state.with("pool", state.pool.set(p, Set()))
    }

    pure def remove(state: MempoolState, p: Process, t: Tx): MempoolState = {
      state.with("pool", state.pool.set(p, state.pool.get(p).exclude(Set(t))))
    }

    pure def update(state: MempoolState, p: Process, txs: Set[Tx]): MempoolState = {
      state.with("pool", state.pool.set(p, state.pool.get(p).union(txs).filter(t => not(isValid(state.abci, t)))))
    }

}

module MempoolTests {

    import Spells.* from "../Common/Spells"
    import System.* from "../Common/System"
    import Ledger.* from "../Ledger/Ledger"
    import Mempool.*
    import ABCI.*

    pure val PROCESSES=Set("alice", "bob", "charlie")
    pure val TXS=Set("T0", "T1", "T2", "T3")

    var ledger: LedgerState
    var abci: ABCIState
    var mempool: MempoolState
    
    action init : bool = all {
      val nledger = newLedger(PROCESSES)
      val nabci = newABCI(nledger)
      all {
        ledger' = nledger,
        abci' = nabci,
        mempool' = newMemPool(PROCESSES, nabci),
      }
    }

    action doClient(p: Process, t: Tx): bool = all {
      all {
        require(isValid(abci, t)),
	ledger' = ledger,
	abci' = abci,
        mempool' = add(mempool, p, t)
      }
    }

    action doSubmit(p: Process): bool = all {
      val txs = reap(mempool, p, 1)
      all {
        require(txs.forall(t => isValid(abci, t)) and maySubmit(ledger, p, txs)),
	ledger' = submit(ledger, p, txs),
	abci' = abci,
      	mempool' = mempool
      }
    }

    action doCommitThenUpdate(p: Process): bool = all {
      val nledger = if (mayCommit(ledger, p)) commit(ledger, p) else ledger
      val nmempool = if (heightOf(ledger, p)!=heightOf(nledger, p)) update(mempool, p, lastEntry(nledger, p)) else mempool
      all {
        require(mayCommit(ledger, p)),
	ledger' = nledger,
	abci' = abci,
        mempool' = mempool
      }
    }

    action step: bool = {
      nondet p = oneOf(PROCESSES)
      nondet t = oneOf(TXS)
      any {
        doClient(p,t),
        doSubmit(p),
	doCommitThenUpdate(p)
      }	
    }

    // INVARIANTS
    
    // INV1. the mempool is used as an input for the ledger
    // trivial from the code of doSubmit
    
    // INV2. every committed transaction is eventually removed forever from the mempool
    def gcInv() = {
      PROCESSES.forall(p => 0.to(heightOf(ledger, p)).forall(i =>  entry(ledger, p, i).intersect(poolOf(mempool, p)).size()==0))      
    }

    // INV3. every transaction in the mempool is valid
    def validInv() = {
      PROCESSES.forall(p => poolOf(mempool, p).forall(t => isValid(abci, t)))
    }

    temporal alwaysInv: bool = always(validInv and gcInv)
    
    // INV4. every transaction that appears in the mempool is eventually committed or forever invalid
    // cannot be checked so far, instead we check if after enough step the mempool is empty

    // run moveHeightOnce = {
    //   nondet p = oneOf(PROCESSES)
    //   nondet t = oneOf(TXS)
    //   init
    //   .then(doClient(p,t))
    //   .then(doSubmit(p))
    //   .then(doCommitThenUpdate(p))
    // }

}

