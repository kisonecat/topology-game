import Game.Metadata

World "SpaceWorld"
Level 3
Title "Proving Something New!"

Introduction "
Of course, if the intersection of two opens must be open,
we should be able to prove three open sets have open intersection.
"

open Set Topology

variable {X : Type} [TopologicalSpace X]

Statement (U V W : Set X) (U_open : IsOpen U)
    (V_open : IsOpen V) (W_open : IsOpen W) : IsOpen (U ∩ V ∩ W) := by
  Hint "
  You should be able to do this with two `apply`s and three `exact`s.
  "
  apply IsOpen.inter
  apply IsOpen.inter
  exact U_open
  exact V_open
  exact W_open

Conclusion "Awesome job!"
