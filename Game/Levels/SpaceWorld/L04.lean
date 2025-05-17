import Game.Metadata

World "SpaceWorld"
Level 4
Title "Inductive Arguments"

Introduction "
We could now prove `IsOpen (U ∩ V ∩ W ∩ S)`, but the smarter play
is to prove any finite intersection is open.
"

open Set Topology Nat

variable {X : Type}

NewTactic induction' simp

/--
By definition, the intersection of two open sets is open.
-/
TheoremDoc Set.biInter_lt_succ as "biInter_lt_succ" in "Set"
NewTheorem Set.biInter_lt_succ



Statement (h: TopologicalSpace X) (n : ℕ) (U: ℕ → Set X)
    (U_open : ∀ m : ℕ, IsOpen (U m)) : IsOpen (⋂ m < n, U m) := by
  Hint "
  Informally, in this scenario we have $n \\in \\mathbb\{N}$,
  and open sets $U_n$ is open for all $n \\in \\mathbb\{N}$.
  We wish to prove that $\\bigcap_\{m\\leq n} U_m$ is open.
  "
  induction' n with n hn
  simp
  simp [biInter_lt_succ]
  apply h.isOpen_inter
  exact hn
  exact U_open n


Conclusion "Awesome job!"
