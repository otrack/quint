// -*- mode: Bluespec; -*-
module Consensus{

    import Spells.* from "./Spells"
    import System.* from "./System"

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

    import Spells.* from "./Spells"
    import System.* from "./System"
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
