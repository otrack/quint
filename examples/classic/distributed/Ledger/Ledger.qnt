// -*- mode: Bluespec; -*-
module Spells{
    def require(cond: bool): bool = cond

    def setEquals(s: Set[x], t: Set[x]): bool = {
      s.size()==t.size() and s.forall(y => t.contains(y))
    }

    def setEqualsOrOneEmpty(s: Set[x], t: Set[x]): bool = {
      (s.size()==0 or t.size()==0) or setEquals(s,t)
    }

    def setExists(s: Set[x], cond: x => bool): bool = {
      s.fold(false, (result, elem) => result or cond(elem))
    }

}

module System{
    type Process = str
    type Tx = str

    pure val PROCESSES = Set("alice", "bob", "charlie")
    pure val TXS = Set("t0", "t1", "t2")
}

module Consensus{

    import Spells.*
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

    pure def propose(state: ConsensusState, p: Process, txs: Set[Tx]): ConsensusResult = {
      val res = PROCESSES.contains(p) and not(hasProposed(state, p)) and txs.size()!=0
      val newProposed = state.proposed.set(p, txs)
      returnConsensusResult(state.with("proposed", newProposed), res)
    }

    pure def decide(state: ConsensusState, p: Process): ConsensusResult = {
      val res = PROCESSES.contains(p) and state.hasProposed(p) and not(state.hasDecided(p))
      val st = if(res) {
	  val proposal = state.proposed.get(oneOf(state.proposed.keys().filter(x => state.proposed.get(x).size()>0)))
          val decisions = state.decided.keys().filter(x => state.decided.get(x).size()>0)
          val decision = if (decisions.size()>0) {state.decided.get(oneOf(decisions))}  else {proposal}
          val newDecided = state.decided.set(p, decision)
          state.with("decided",newDecided)
	}else{
	  state
	}
      returnConsensusResult(st, res)      
    }

    // INVARIANTS
    
    // Irrevocability: a process decides at most once
    // [Trivial from the preconditions in Consensus::decide.]
    
    // Validity: a process decides only submitted values
    // [Trivial from the preconditions in Consensus::decide.]
    
    // Agreement: no two processes decide different values
    pure def consensusAgreementInv(state: ConsensusState): bool = {
       PROCESSES.forall(x => PROCESSES.forall(y => setEqualsOrOneEmpty(state.decided.get(x), state.decided.get(y))))
    }

}

module ConsensusTests {

    import Spells.*
    import System.*
    import Consensus.*

    action initConsensusTests = all {
        true
    }

    run proposeTwiceError = {
      initConsensusTests.then(
        nondet p = oneOf(PROCESSES)
        nondet tx = oneOf(TXS)
        val st = propose(newConsensus, p, Set(tx)).state
	not(propose(st, p, Set(tx)).result)
      )
    }

    run decideNonProposedError = {
      initConsensusTests.then(
        nondet p = oneOf(PROCESSES)
    	not(decide(newConsensus, p).result)
      )
    }

    run decideProposedSuccess = {
      initConsensusTests.then(
        nondet p = oneOf(PROCESSES)
    	nondet q = oneOf(PROCESSES)
    	nondet tx0 = oneOf(TXS)
    	nondet tx1 = oneOf(TXS)
    	val st = propose(propose(newConsensus, p, Set(tx0)).state, q, Set(tx1)).state
    	decide(st, p).result
      )
    }

}

// A Ledger is a replicated log of set of transactions (aka. blocks).
// The definition below considers that
// - replication is made with consensus (SMR)
// - idempotence is not granter (that is, two entries might have common values).
module Ledger{

    import Spells.*
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

    pure def submit(state: LedgerState, p: Process, txs: Set[Tx]): LedgerResult = {
      val currentConsensus = state.log[heightOf(state,p)]
      if (currentConsensus.hasProposed(p)) {
        returnLedgerResult(state, false)
      } else {
        val nextLog = state.log.replaceAt(heightOf(state,p), currentConsensus.propose(p, txs).state)
	returnLedgerResult(state.with("log", nextLog), true)
      }
    }

    pure def commit(state: LedgerState, p: Process): LedgerResult = {
      val currentConsensus = state.log[heightOf(state,p)]
      if (not(currentConsensus.hasProposed(p)) or currentConsensus.hasDecided(p)) {
        returnLedgerResult(state, false)
      } else {
        val nextLog = if (heightOf(state, p) == height(state)) {
	  state.log.append(newConsensus)
	}else{
	  state.log
	}
    	returnLedgerResult(state.with("log", nextLog.replaceAt(heightOf(state,p), currentConsensus.decide(p).state)), true)
      }
    }

    // INVARIANTS
    
    // Validity: every entry is submitted
    // {Trivial from the precondition in Ledger:commit.]
    
    // Agreement: for any two processes, entries are prefix one from another
    pure def LedgerAgreementInv(state: ConsensusState): bool = {
      val p = oneOf(PROCESSES)
      0.to(height(state)).forall(h => consensusAgreementInv(state.log[h]))
    }

}

module LedgerTests {

    import Spells.*
    import System.*
    import Ledger.*

    action initLedgerTests = all {
        true
    }

    run submitTwiceError = {
      initLedgerTests.then(
        nondet p = oneOf(PROCESSES)
        nondet tx = oneOf(TXS)
        val st = submit(newLedger, p, Set(tx)).state
	not(submit(st, p, Set(tx)).result)
      )
    }

    run commitNonProposedError = {
      initLedgerTests.then(
        nondet p = oneOf(PROCESSES)
    	not(commit(newLedger, p).result)
      )
    }

    run decideProposedSuccess = {
      initLedgerTests.then(
        nondet p = oneOf(PROCESSES)
    	nondet q = oneOf(PROCESSES)
    	nondet tx0 = oneOf(TXS)
    	nondet tx1 = oneOf(TXS)
    	val st = submit(submit(newLedger, p, Set(tx0)).state, q, Set(tx1)).state
    	commit(st, p).result
      )
    }

}
