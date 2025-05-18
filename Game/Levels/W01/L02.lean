import Game.Metadata

World "AxiomWorld"
Level 2
Title "The Intersection Axiom"

Introduction "
The next axiom of topological spaces is that
every pair of open sets must have an open intersection.
"


NewTactic apply

/--
By definition, the intersection of two open sets is open.
-/
TheoremDoc IsOpen.inter as "IsOpen.inter" in "Topology"
NewTheorem IsOpen.inter


open Set Topology
variable {X : Type} [TopologicalSpace X]


Statement (U V : Set X) (U_open : IsOpen U) (V_open : IsOpen V) :
    IsOpen (U ∩ V) := by
  Hint "
  Again, we have little to prove here: this should just be
  intersection axiom. The way this theorem is stated
  in Lean is a little different than the way it's expressed here, however.
  (Try typing `exact IsOpen.inter` and see what happens!)

  So it's not `exact`ly the same, but `IsOpen.inter` is certainly still
  applicable! In fact, we can use the `apply` tactic here rather than
  `exact`...
  "
  apply IsOpen.inter
  Hint "
  Great! By `apply`ing `IsOpen.inter`, you've reduced our goal of
  `IsOpen (U ∩ V)` into two subgoals, which are `exact`ly our
  two assumptions `U_open` and `V_open`.
  So use two `exact` statements to complete
  this proof.
  "
  exact U_open
  exact V_open

Conclusion "Good work!"
