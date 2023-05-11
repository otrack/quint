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
