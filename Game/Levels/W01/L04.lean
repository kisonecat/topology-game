import Game.Metadata

World "SpaceWorld"
Level 4
Title "Inductive Arguments"

Introduction "
We could now prove `IsOpen (U ∩ V ∩ W ∩ S)`, but the smarter play
is to prove any finite intersection is open.
"

NewTactic induction' simp rw

/--
Splits up an intersection over a successor ordinal into a binary
intersection of with the last element and the rest of the intersection.
-/
TheoremDoc Set.biInter_lt_succ as "biInter_lt_succ" in "Set"
NewTheorem Set.biInter_lt_succ


open Set Topology Nat
variable {X : Type} [TopologicalSpace X]

Statement (n : ℕ) (U: ℕ → Set X)
    (U_open : ∀ m : ℕ, IsOpen (U m)) : IsOpen (⋂ m < n, U m) := by
  Hint "
  Informally, in this scenario we have $n \\in \\mathbb\{N}$,
  and open sets $U_n$ for all $n \\in \\mathbb\{N}$.
  We wish to prove that $\\bigcap_\{m<n} U_m$ is open.
  "
  Hint "
  To prove this, we will need to use induction. This is possible
  using mathlib's `induction'` tactic. (There is also an `induction` tactic,
  but this variation allows for a cleaner proof.) Try using
  `induction' n with n ind_hyp` to split your goal into a base case and
  a successor case.
  "
  induction' n with n ind_hyp
  Hint "
  This base case $\\bigcap_\{m<0} U_m$ is trivial, which is a great
  opportunity to show off mathlib's `simp` tactic. Just run `simp`
  and Lean will automatically prove this trivial base case for us by
  realizing $\\bigcap_\{m<0} U_m$
  is an intersection over an empty collection, and is thus equal to `univ`,
  which is always open.
  "
  simp
  Hint "
  Now here, `simp` is not smart enough to prove this case for us (try it).
  However, we can use the `biInter_lt_succ` lemma that
  $\\bigcap_\{m<n+1} U_m = (\\bigcap_\{m<n} U_m) \\cap U_n$ to `rewrite` the goal
  into a binary intersection which we can handle given our induction hypothesis.
  Try `rw [biInter_lt_succ]` to see how this works.
  "
  rw [biInter_lt_succ]
  Hint "
  Now we can `apply` the basic fact that the intersection of two open sets is open.
  "
  apply IsOpen.inter
  Hint "
  This is exactly our induction hypothesis, which we named `ind_hyp`.
  "
  exact ind_hyp
  Hint "
  Here we can `apply` the hypothesis `U_open`, or we could note that
  this is `exact`ly `U_open` for the value of `n`, that is, `exact U_open n`.
  "
  exact U_open n

Conclusion "Awesome job!"
