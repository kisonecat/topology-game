import Game.Metadata

World "AxiomWorld"
Level 1
Title "The Universal Axiom"

Introduction "
In mathematics, a `TopologicalSpace` is a `Set` paired
with a family of \"open subsets\". This family, called a topology,
must satisfy three axioms. The first is that the entire set itself
must be an open subset.
"

NewTactic exact

/--
By definition, the universe `univ` is always open in a topological
space.
-/
TheoremDoc isOpen_univ as "isOpen_univ" in "Topology"
NewTheorem isOpen_univ


open Set Topology
variable {X : Type} [TopologicalSpace X]

Statement : IsOpen (univ : Set X) := by
  Hint "
  There's nothing to prove here. `IsOpen univ` is `exact`ly the
  first axiom of `X` being a topological space.

  To say this in Lean, write `exact isOpen_univ`. The `exact`
  tactic says that the goal is exactly a known fact. Then `isOpen_univ`
  specifically says that the universe of a topological space is open.
  "
  exact isOpen_univ

Conclusion "Great first proof!"
