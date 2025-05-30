import Game.Metadata

World "ContinuityWorld"
Level 1
Title "Mapping out of the discrete"

/-- yada yada -/
TheoremDoc continuous_def as "continuous_def" in "Continuity"
NewTheorem continuous_def

Introduction "
Our first task is to prove that every function
from a *discrete* topological space to a topological space
is continuous.
"

open Set Topology
variable {X : Type}
variable {Y : Type}
variable {f : X → Y}

variable [TopologicalSpace X]
variable [TopologicalSpace Y]

variable (h : ∀ (s : Set X), IsOpen s)

Statement : Continuous f := by
  rw [continuous_def]
  rintro s hs
  apply h

Conclusion "You did it!"
