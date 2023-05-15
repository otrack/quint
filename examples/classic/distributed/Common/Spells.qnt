// -*- mode: Bluespec; -*-
module Spells{
    def require(cond: bool): bool = cond

    def setEqualsOrOneEmpty(s: Set[x], t: Set[x]): bool = {
      (s.size()==0 or t.size()==0) or s == t
    }

    def setSubsetOfAtMost(s: Set[x], max: int): Set[x] = {
      if (max>=size(s)) s else oneOf(s.powerset().filter(u => size(u)==max))
    }

}
