// -*- mode: Bluespec; -*-
module System{
    type Process = str
    type Tx = str

    pure val PROCESSES = Set("alice", "bob", "charlie")
    pure val TXS = Set("t0", "t1", "t2")
}

module Consensus{

    import Spells.* from "../Spells.qnt"
    import System.*

    type ConsensusState = {
      proposed: Process -> Set[Tx],
      decided: Process -> Set[Tx],
    }

    type ConsensusResult = {
      state: ConsensusState,
      result: bool
    }

    pure def returnConsensusResult(state: ConsensusState, result: bool): ConsensusResult = {
        {state: state, result: result}
    }

    pure def newConsensus(): ConsensusState = {
      proposed: PROCESSES.mapBy(x => Set()),
      decided: PROCESSES.mapBy(x => Set())
    }

    pure def hasProposed(state: ConsensusState, p: Process): bool = state.proposed.get(p).size() > 0
    
    pure def hasDecided(state: ConsensusState, p: Process): bool = state.decided.get(p).size() > 0

    pure def isDecided(state: ConsensusState): bool = state.decided.keys().filter(x => state.decided.get(x).size()>0).size() > 0

    pure def decisionOf(state: ConsensusState, p: Process): Set[Tx] = state.decided.get(p)

    pure def mayPropose(state: ConsensusState, p: Process, txs: Set[Tx]): bool = PROCESSES.contains(p) and not(hasProposed(state, p)) and txs.size()!=0

    pure def mayDecide(state: ConsensusState, p: Process): bool = PROCESSES.contains(p) and state.hasProposed(p) and not(state.hasDecided(p))

    pure def propose(state: ConsensusState, p: Process, txs: Set[Tx]): ConsensusState = {
      val newProposed = state.proposed.set(p, txs)
      state.with("proposed", newProposed)
    }

    pure def decide(state: ConsensusState, p: Process): ConsensusState = {
      val proposal = state.proposed.get(oneOf(state.proposed.keys().filter(x => state.proposed.get(x).size()>0)))
      val decisions = state.decided.keys().filter(x => state.decided.get(x).size()>0)
      val decision = if (decisions.size()>0) {state.decided.get(oneOf(decisions))}  else {proposal}
      val newDecided = state.decided.set(p, decision)
      state.with("decided",newDecided)
    }

    // INVARIANTS
    
    // Irrevocability: a process decides at most once
    // [Require applying Consensus:mayDecide before Consensus:decide]
    
    // Validity: a process decides only submitted values
    // [Trivial from the code of Consensus:decide]
    
    // Agreement: no two processes decide different values
    pure def consensusAgreementInv(state: ConsensusState): bool = {
       PROCESSES.forall(x => PROCESSES.forall(y => setEqualsOrOneEmpty(state.decided.get(x), state.decided.get(y))))
    }

}

module ConsensusTests {

    import Spells.* from "../Spells.qnt"
    import System.*
    import Consensus.*

    action initConsensusTests = all {
        true
    }

    run proposeTwiceError = {
      initConsensusTests.then(
        nondet p = oneOf(PROCESSES)
        nondet tx = oneOf(TXS)
        val st = propose(newConsensus, p, Set(tx))
	not(mayPropose(st, p, Set(tx)))
      )
    }

    run decideNonProposedError = {
      initConsensusTests.then(
        nondet p = oneOf(PROCESSES)
	not(mayDecide(newConsensus, p))
      )
    }

    run decideProposedSuccess = {
      initConsensusTests.then(
        nondet p = oneOf(PROCESSES)
    	nondet q = oneOf(PROCESSES)
    	nondet tx0 = oneOf(TXS)
    	nondet tx1 = oneOf(TXS)
    	val st = propose(propose(newConsensus, p, Set(tx0)), q, Set(tx1))
	mayDecide(st, p) and hasDecided(decide(st, p), p)
      )
    }

}

// A Ledger is a replicated log of set of transactions (aka. blocks).
// The definition below considers that
// - replication is made with consensus (SMR)
// - idempotence is not granter (that is, two entries might have common values).
module Ledger{

    import Spells.* from "../Spells.qnt"
    import System.*
    import Consensus.*
    
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

    import Spells.* from "../Spells.qnt"
    import System.*
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
