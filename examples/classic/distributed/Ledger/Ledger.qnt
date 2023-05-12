// -*- mode: Bluespec; -*-
// A Ledger is a replicated log of blocks.
// The definition below considers that
// - replication is made with consensus (SMR)
// - idempotence is not granted (that is, two entries might have transactions in common).
module Ledger{

    import Spells.* from "./Spells"
    import System.* from "./System"
    import Consensus.* from "./Consensus"

    type LedgerState = {
      log: List[ConsensusState],
    }

    pure def newLedger(P: Set[Process]): LedgerState = {log: List(newConsensus(P))}

    pure def height(state: LedgerState): int = length(state.log.select(s => s.isDecided()))

    pure def heightOf(state: LedgerState, p: Process): int = length(state.log.select(s => s.hasDecided(p)))

    pure def entry(state: LedgerState, p: Process, i: int): Set[Tx] = state.log[i].decisionOf(p)

    pure def maySubmit(state: LedgerState, p: Process, txs: Set[Tx]): bool = {
      val currentConsensus = state.log[heightOf(state,p)]
      txs.size()>0 and not(currentConsensus.hasProposed(p))
    }

    pure def mayCommit(state: LedgerState, p: Process): bool = {
      val currentConsensus = state.log[heightOf(state,p)]
      currentConsensus.hasProposed(p) and not(currentConsensus.hasDecided(p))
    }

    pure def submit(state: LedgerState, p: Process, txs: Set[Tx]): LedgerState = {
      val currentConsensus = state.log[heightOf(state,p)]
      val nextLog = state.log.replaceAt(heightOf(state,p), currentConsensus.propose(p, txs))
      state.with("log", nextLog)
    }

    pure def commit(state: LedgerState, p: Process): LedgerState = {
      val currentConsensus = state.log[heightOf(state,p)]
      val nextLog = if (heightOf(state, p) == height(state)) {
          state.log.append(newConsensus(processes(state.log[0])))
      }else{
    	  state.log
      }
      state.with("log", nextLog.replaceAt(heightOf(state,p), currentConsensus.decide(p)))
    }

    // INVARIANTS
    
    // Validity: every entry is submitted
    pure def ledgerValidityInv(state: LedgerState): bool = {
      0.to(height(state)).forall(h => consensusValidityInv(state.log[h]))
    }
    
    // Order: for any two processes, entries are prefix one from another
    pure def ledgerOrdertInv(state: LedgerState): bool = {
      0.to(height(state)).forall(h => consensusAgreementInv(state.log[h]))
    }

}

module LedgerTests {

    import Spells.* from "./Spells"
    import System.* from "./System"
    import Ledger.*

    pure val PROCESSES=Set("alice", "bob", "charlie")
    pure val TXS=Set("t0", "t1", "t2")

    var st: LedgerState

    val invariant: bool = {
      ledgerValidityInv(st) and ledgerOrdertInv(st)
    }

    action init = all {
        st' = newLedger(PROCESSES)
    }

    action doSubmit = all {
      nondet p = oneOf(PROCESSES)
      nondet tx = oneOf(TXS)
      all {
        require(maySubmit(st, p, Set(tx))),
    	st' = submit(st, p, Set(tx))
      }
    }

    action doCommit = all {
      nondet p = oneOf(PROCESSES)
      all {
        require(mayCommit(st, p)),
	st' = commit(st, p)
      }
    }

    action step = any {
      doSubmit,
      doCommit
    }

    run submitTwiceError = {
      nondet p = oneOf(PROCESSES)
      nondet tx = oneOf(TXS)
      init
      .then(
        all {
	  maySubmit(submit(st, p, Set(tx)), p, Set(tx)),
	  st'=st
	}
      )
      .fail()
    }

    run commitNonSubmittedError = {
      nondet p = oneOf(PROCESSES)
      init
      .then(
        all {
    	  mayCommit(st, p),
	  st'=st
	}
      )
      .fail()
    }

    run commitSubmittedSuccess = {
      nondet p = oneOf(PROCESSES)
      nondet q = oneOf(PROCESSES)
      nondet tx0 = oneOf(TXS)
      nondet tx1 = oneOf(TXS)
      init
      .then(st'=submit(submit(st, p, Set(tx0)), q, Set(tx1)))
      .then(
        all {
	  mayCommit(st, p) and heightOf(commit(st, p), p)==1,
	  st'=st
	}
      )
    }

}
