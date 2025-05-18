import Game.Metadata

World "AxiomWorld"
Level 6
Title "An Empty Feeling"

Introduction "
You might think we forgot a common \"axiom\" of topological
spaces: the empty set must always be open. But in fact, this
is guaranteed by the other three axioms.
"

/--
Proof that `⋃₀ ∅ = ∅`.
-/
TheoremDoc Set.sUnion_empty as "sUnion_empty" in "Set"
NewTheorem Set.sUnion_empty

open Set Topology Nat

variable {X : Type} [TopologicalSpace X]

Statement : IsOpen (∅: Set X) := by
  Hint "
  You can use `sUnion_empty` to rewrite this goal into a goal
  that can be addressed by one of the three axioms.
  "
  rw [← sUnion_empty]
  Hint "
  Now apply the right topological axiom.
  "
  apply isOpen_sUnion
  Hint "
  Hmm, this seems rather trivial! Maybe Lean can knock this out
  with one word?
  "
  simp

Conclusion "Awesome job!"
