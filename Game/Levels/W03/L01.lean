import Game.Metadata

World "ContinuityWorld"
Level 1
Title "Mapping into the indiscrete"

Introduction "
Our first task is to prove that every function
from a *discrete* topological space to a topological space
is continuous.
"

/-- yada yada -/
TheoremDoc absurd as "absurd" in "Logic"
/-- yada yada -/
TheoremDoc TopologicalSpace.mk as "TopologicalSpace.mk" in "Topology"
/-- yada yada -/
TheoremDoc Set.eq_univ_iff_forall as "eq_univ_iff_forall" in "Set"

NewTheorem TopologicalSpace.mk Set.eq_univ_iff_forall absurd

NewTactic right left by_cases obtain «have»

open Set Topology
variable {X : Type}
variable {Y : Type}
variable {f : X → Y}

variable [TopologicalSpace X]
variable [TopologicalSpace Y]
variable [DiscreteTopology Y]

Statement : Continuous f := by
  sorry

Conclusion "Whew, you did it!"
