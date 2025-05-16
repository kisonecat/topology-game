import Game.Metadata

World "SpaceWorld"
Level 1

Title "Your First Space"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

/- Use these commands to add items to the game's inventory. -/

open Set Topology

variable {X : Type}

Statement (g: TopologicalSpace X) :
    IsOpen (univ : Set X) ∧ IsOpen (univ : Set X) := by
  constructor
  · exact isOpen_univ
  · exact isOpen_univ
  -- Hint "You can either start using `{h}` or `{g}`."
  -- Branch
  --   rw [g]
  --   Hint "You should use `{h}` now."
  --   rw [h]
  -- rw [h]
  -- Hint "You should use `{g}` now."
  -- rw [g]

Conclusion "This last message appears if the level is solved."

NewTactic exact constructor

/--
some description
-/
TheoremDoc TopologicalSpace.isOpen_univ as "isOpen_univ" in "foo"

NewTheorem TopologicalSpace.isOpen_univ
