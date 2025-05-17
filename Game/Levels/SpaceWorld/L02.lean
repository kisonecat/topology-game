import Game.Metadata

World "SpaceWorld"
Level 2
Title "The Intersection Axiom"

Introduction "
The next axiom of topological spaces is that
every pair of open sets must have an open intersection.
"

/- Use these commands to add items to the game's inventory. -/

open Set Topology

variable {X : Type}

NewTactic apply

/--
By definition, the intersection of two open sets is open.
-/
TheoremDoc TopologicalSpace.isOpen_inter as "h.isOpen_inter" in "Topology"
NewTheorem TopologicalSpace.isOpen_inter

Statement (h: TopologicalSpace X) (U V : Set X)
    (U_open : IsOpen U) (V_open : IsOpen V) : IsOpen (U ∩ V) := by
  Hint "
  Again, we have little to prove here: this should just be
  intersection axiom. The way this theorem is stated
  in Lean is a little different than the way it's expressed here, however.
  (Try typing `exact h.isOpen_inter` and see what happens!)

  So it's not `exact`ly the same, but `h.isOpen_inter` is certainly still
  applicable! In fact, we can use the `apply` tactic here rather than
  `exact`...
  "
  apply h.isOpen_inter
  Hint "
  Great! By `apply`ing `h.isOpen_inter`, you've reduced our goal to show
  `IsOpen (U ∩ V)` into two subgoals. The first subgoal is `IsOpen U`, which
  is `exact`ly one of our hypotheses...
  "
  exact U_open
  Hint "
  And the second subgoal is also a given hypothesis.
  "
  exact V_open

Conclusion "Good work!"
