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

    var proposed: Process -> Set[Tx]
    var decided: Process -> Set[Tx]

    val consensus = {proposed: proposed, decided: decided}

    def hasProposed(p: Process): bool = proposed.get(p).size() != 0
    
    def hasDecided(p: Process): bool = decided.get(p).size() != 0

    action initConsensus: bool = all {
      proposed' = PROCESSES.mapBy(x => Set()),
      decided' = PROCESSES.mapBy(x => Set()),
    }

    action propose(p: Process, txs: Set[Tx]): bool = all {
      require(PROCESSES.contains(p)),
      require(not(hasProposed(p))),
      require(txs.size()!=0),
      all {
        proposed' = proposed.set(p, txs),
    	decided' = decided,
      }
    }

    action decide(p: Process, txs: Set[Tx]): bool = all {
      require(txs.size()!=0),
      require(PROCESSES.contains(p)),
      require(not(hasDecided(p))),
      require(setExists(PROCESSES, x => setEquals(proposed.get(x), txs))),
      require(PROCESSES.forall(x => setEqualsOrOneEmpty(decided.get(x), txs))),
      all {
        proposed' = proposed,
      	decided' = decided.set(p, txs),
      }
    }

    action noop: bool = all {
      proposed' = proposed,
      decided' = decided,
    }

    action stepConsensus: bool = {
      nondet p = oneOf(PROCESSES)
      nondet tx = oneOf(TXS)
      any{
	propose(p, Set(tx)),
	decide(p, Set(tx)),
      }
    }

    // INVARIANTS
    // Irrevocability and Validity are both trivial from the definition of Consensus::decide.
    // Agreement
    val agreementInv: bool = {
       PROCESSES.forall(x => PROCESSES.forall(y => setEqualsOrOneEmpty(decided.get(x),decided.get(y))))
     }

    temporal Agreement: bool = always(agreementInv)

    run proposeTwiceError = {
      nondet p = oneOf(PROCESSES)
      nondet tx = oneOf(TXS)
      initConsensus.then(propose(p, Set(tx)))
          .then(propose(p, Set(tx)))
	  .fail()
    }

    run proposeDecideNonProposedError = {
      nondet p = oneOf(PROCESSES)
      nondet tx = oneOf(TXS)
      initConsensus.then(propose(p, Set(tx)))
          .then(decide(p, Set(tx)))
	  .fail()
    }

}

module SMR{

    import Spells.*
    import System.*
    import Consensus.*
    
    var log: List[consensus]
    var height: Process -> int

    // FIXME can we do this dynamically? ("import" is not allowed in an action)
    import Consensus as C1
    import Consensus as C2
    import Consensus as C3
    
    action initBlockchain: bool = all {
      log' = List(C1::consensus, C2::consensus, C3::consensus),
      height' = PROCESSES.mapBy(x => 0),
    }   

    // FIXME cannot apply the state transition operators to the consensus instances
    // action submit(p: Process, txs: Set[Tx]): bool = all {
    //   require(height.get(p) == 0 or log.nth(height.get(p)-1).decided.get(p)),
    //   height' = height.set(p, height.get(p)+1),
    //   log.nth(height.get(p)).decided,
    //   log' = log,
    // }

}
