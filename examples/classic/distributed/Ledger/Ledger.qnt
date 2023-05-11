// -*- mode: Bluespec; -*-
// A Ledger is a replicated log of set of transactions (aka. blocks).
// The definition below considers that
// - replication is made with consensus (SMR)
// - idempotence is not granter (that is, two entries might have common values).
module Ledger{

    import Spells.* from "./Spells"
    import System.* from "./System"
    import Consensus.* from "./Consensus"
    
    type LedgerState = {
      log: List[ConsensusState],
    }

    type LedgerResult = {
      state: LedgerState,
      result: bool
    }

    pure def returnLedgerResult(state: LedgerState, result: bool): LedgerResult = {state: state, result: result}

    pure def newLedger(): LedgerState = {log: List(newConsensus)}

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
          state.log.append(newConsensus)
      }else{
    	  state.log
      }
      state.with("log", nextLog.replaceAt(heightOf(state,p), currentConsensus.decide(p)))
    }

    // INVARIANTS
    
    // Validity: every entry is submitted
    // {Trivial from the code in Ledger:commit.]
    
    // Agreement: for any two processes, entries are prefix one from another
    pure def LedgerAgreementInv(state: ConsensusState): bool = {
      val p = oneOf(PROCESSES)
      0.to(height(state)).forall(h => consensusAgreementInv(state.log[h]))
    }

}

module LedgerTests {

    import Spells.* from "./Spells"
    import System.* from "./System"
    import Ledger.*

    action initLedgerTests = all {
        true
    }

    run submitTwiceError = {
      initLedgerTests.then(
        nondet p = oneOf(PROCESSES)
        nondet tx = oneOf(TXS)
        val st = submit(newLedger, p, Set(tx))
	not(maySubmit(st, p, Set(tx)))
      )
    }

    run commitNonSubmittedError = {
      initLedgerTests.then(
        nondet p = oneOf(PROCESSES)
    	not(mayCommit(newLedger, p))
      )
    }

    run commitSubmittedSuccess = {
      initLedgerTests.then(
        nondet p = oneOf(PROCESSES)
    	nondet q = oneOf(PROCESSES)
    	nondet tx0 = oneOf(TXS)
    	nondet tx1 = oneOf(TXS)
    	val st = submit(submit(newLedger, p, Set(tx0)), q, Set(tx1))
    	mayCommit(st, p) and heightOf(commit(st, p), p)==1
      )
    }

    // some random run of length k

}
