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

NewTactic induction' simp rw

/--
Splits up an intersection over a successor ordinal into a binary
intersection of with the last element and the rest of the intersection.
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
  Hint "
  To prove this, we will need to use induction. This is possible
  using mathlib's `induction'` tactic. (There is also an `induction` tactic,
  but this variation allows for a cleaner proof.) Try using
  `induction' n with n hn` to split your goal into a base case and
  a successor case.
  "
  induction' n with n hn
  Hint "
  This base case is trivial, but would be tedious to work through explicitly.
  Fortunately, we can use the `simp` tactic to help us out. Just run `simp`
  and Lean will automatically prove the base case for us by realizing this
  is an intersection over an empty collection, which is equal to `univ`,
  which is always open.
  "
  simp
  Hint "
  Now here, `simp` is not smart enough to prove this case for us.
  However, we can use the `biInter_lt_succ` lemma to `rewrite` the goal
  into a binary intersection which we can handle given our induction hypothesis.
  Try `rw [biInter_lt_succ]` to see how this works.
  "
  rw [biInter_lt_succ]
  Hint "
  Remember how to turn a goal asking to prove that the binary intersection of
  two sets is open into a goal asking to prove that each of the two sets
  is open?
  "
  apply h.isOpen_inter
  Hint "
  This is exactly our induction hypothesis, which we named `hn`.
  "
  exact hn
  Hint "
  Here we can `apply` the hypothesis `U_open`, or we could note that
  this is `exact`ly `U_open` for `n`, that is, `exact U_open n`.
  "
  exact U_open n

Conclusion "Awesome job!"
