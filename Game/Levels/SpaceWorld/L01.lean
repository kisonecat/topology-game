import Game.Metadata

World "SpaceWorld"
Level 1
Title "The Universal Axiom"

Introduction "
In mathematics, a `TopologicalSpace` is a `Set` paired
with a family of \"open subsets\". This family, called a topology,
must satisfy three axioms. The first is that the entire set itself
must be an open subset.
"

/- Use these commands to add items to the game's inventory. -/

open Set Topology

variable {X : Type}

NewTactic exact

/--
By definition, the universe `univ` is always open in a topological
space.
-/
TheoremDoc TopologicalSpace.isOpen_univ as "h.isOpen_univ" in "Topology"
NewTheorem TopologicalSpace.isOpen_univ

Statement (h: TopologicalSpace X) : IsOpen (univ : Set X) := by
  Hint "
  There's nothing to prove here. `IsOpen univ` is `exact`ly the
  first axiom of `X` being a topological space.

  To say this in Lean, write `exact h.isOpen_univ`. The `exact`
  tactic says that the goal is exactly a known fact. Our hypothesis
  `h` is that `X` is a topological space, and `h.isOpen_univ`
  specifically says that the universe of this topological space is open.
  "
  exact h.isOpen_univ

Conclusion "Great first proof!"
