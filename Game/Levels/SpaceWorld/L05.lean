import Game.Metadata

World "SpaceWorld"
Level 5
Title "The Final Axiom"

Introduction "
Finally, we have that the arbitrary union of open sets is open.
"

open Set Topology Nat

variable {X : Type}

/--
By definition, the union of any family of open sets is open.
-/
TheoremDoc TopologicalSpace.isOpen_sUnion as "h.isOpen_sUnion" in "Topology"
NewTheorem TopologicalSpace.isOpen_sUnion

Statement (h: TopologicalSpace X) (U V : Set X) (U_open : IsOpen U)
    (V_open : IsOpen V) : IsOpen (U ∪ V) := by
  Hint "
  So of course, a finite union of open sets should be open. To convince
  Lean of this, we will need to convert this binary union into a union
  of a set.
  "
  have : U ∪ V = ⋃₀ {U, V} := by
    simp only [sUnion_insert]
    simp only [sUnion_singleton]
  rw [this]
  apply h.isOpen_sUnion
  intro t ht
  
  sorry

Conclusion "Awesome job!"
