import Game.Metadata

World "ExampleWorld"
Level 1
Title "A Very Simple Example"

Introduction "
foo
"


open Set Topology
variable {X : Type}

Statement : TopologicalSpace X := by
  apply TopologicalSpace.mk (fun U ↦ U = ∅ ∨ U = univ)
  · right
    rfl
  · rintro U V (g|g) (h|h)
    · left
      rw [g]
      simp
    · left
      rw [g]
      simp
    · left
      rw [h]
      simp
    · right
      rw [g, h]
      simp
  · rintro U U_open
    simp
    by_cases h : ∀ s ∈ U, s = ∅
    · left
      exact h
    · right
      simp at h
      obtain ⟨V, hVU, hV⟩ := h
      rw [eq_univ_iff_forall]
      intro x
      use V
      constructor
      · exact hVU
      · have : V = ∅ ∨ V = univ := U_open V hVU
        have : V = univ := by
          cases this
          · exfalso
            apply hV
            exact h
          · exact h
        rw [this]
        simp

Conclusion "Great first proof!"
