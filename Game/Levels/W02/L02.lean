import Game.Metadata

World "ExampleWorld"
Level 2
Title "Let's Be Discrete"

Introduction "
foo
"

open Set Topology
variable {X : Type}

Statement : ∃ h : TopologicalSpace X, U ⊆ (univ : Set X) → h.IsOpen U := by
  have h := TopologicalSpace.generateFrom ({{x} | x : X})
  use h
  intro g
  apply isOpen_sUnion
  rintro t ht
  apply TopologicalSpace.isOpen_generateFrom_of_mem ht



Conclusion "Whew, you did it!"
