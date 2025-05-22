import Game.Metadata

World "ExampleWorld"
Level 1
Title "A (The) Trivial Example"

Introduction "
Our first task in this world is to prove that
topological spaces exist in the first place! And
what better place to start by showing that the
indiscrete/trivial topology is a topology on any set?
"

/-- yada yada -/
TheoremDoc absurd as "absurd" in "Logic"
/-- yada yada -/
TheoremDoc TopologicalSpace.mk as "TopologicalSpace.mk" in "Topology"
/-- yada yada -/
TheoremDoc Set.eq_univ_iff_forall as "eq_univ_iff_forall" in "Set"
NewTheorem TopologicalSpace.mk Set.eq_univ_iff_forall absurd

NewTactic right left by_cases obtain «have»

open Set Topology
variable {X : Type}

Statement : TopologicalSpace X := by
  Hint "
  Our goal is just `TopologicalSpace X`: there exists a
  topology on $X$. To do this directly, we will need to
  `apply TopologicalSpace.mk (fun U ↦ U = ∅ ∨ U = univ)`.
  Here, `U = ∅ ∨ U = univ` prepresents the requirements for a set to
  be open, namely, it should equal the empty set or the universe.
  (To type `∅`, type `\\empty` and then `[Space]` to autocomplete.)
  "
  apply TopologicalSpace.mk (fun U ↦ U = ∅ ∨ U = univ)
  · Hint "
    We now have three goals. The first of these is to verify that
    our condition `U = ∅ ∨ U = univ` for `U` being open guarantees that the
    universe will be open, that is, `univ = ∅ ∨ univ = univ`.
    "
    Hint "
    In Lean, proving a disjunction (\"or\") statement can be accomplished by
    the `right` and `left` tactics. Choosing `right` will reduce this goal to
    proving the right side of the disjunction, and choosing `left` will, well,
    you probably get it. Which one can we verify?
    "
    right
    Hint "
    Seems pretty `simp`le to me. (Actually, we could have used `simp` in the
    previous step, and Lean would have verified this out for us as well!)
    "
    simp
  · Hint "
    This long goal is asking us to verify the finite intersection axiom.
    Just as we did in the previous world, we can prove a statement with a
    universal quantifier and various hypotheses by using `rintro`. Let's
    start by calling our open sets `U` and `V` with `rintro U V`.
    "
    rintro U V
    Hint "
    We now need to prove a statement of the form `P → R → Q`, that is,
    \"If $U$ is open, then if $V$ is open, then $U\\cap V$ is open\".
    Since each assertion that a set is open is a disjunction of two conditions
    (either the set is `∅` or `univ`), we have four cases to check.
    "
    Hint "
    One way to do this is to use `rintro (g|g) (h|h)`, which sets `g` to
    be either `U = ∅` or `U = univ`, and sets `h` to be either `V = ∅`
    or `V = ∅`. (If we wanted, we could have used `rintro U V (g|g) (h|h)`
    at the previous step to do this all at once.)
    "
    rintro (g|g) (h|h)
    · Hint "
      We now need to prove `U ∩ V = ∅ ∨ U ∩ V = univ` for each of
      the four cases. This can be accomplished by `r`e`w`riting the goal
      to substitute `∅` and `univ` appropriately into the goal. In every
      case, it's pretty `simp`le for Lean to wrap things up for us.
      "
      Hint "
      (If doing this four times seems tedious, don't worry; there is Lean
      magic that could have been used to make this more efficient, but we're
      gonna stick to the basics for now.)
      "
      rw [g]
      simp
    · rw [g]
      simp
    · rw [h]
      simp
    · rw [g, h]
      simp
  · Hint "
    Finally, we must verify the union axiom. Let's `rintro`duce `U_col`
    as our collection of sets, and `U_col_open` as the assumption each set
    in the collection is open.
    "
    rintro U_col U_col_open
    Hint "
    Lean can `simp`lify things here: a union is only empty in the case that
    every set in the collection is empty.
    "
    simp
    Hint "
    Here, we cannot proceed with `right` or `left`, because
    we don't know which condition is satisfied for our `U_col`.
    So here we will use `by_cases h : ∀ s ∈ U_col, s = ∅`
    to split our goal into two cases.
    "
    by_cases h : ∀ s ∈ U_col, s = ∅
    · Hint "
      Here our `h` is `exact`ly the `left` side of our
      disjunction.
      "
      left
      exact h
    · Hint "
      Now `h` tells us the `left` side cannot hold,
      so we should move to the `right`.
      "
      right
      Hint "
      The negation of a universal quantifier is an
      existential statement. `simp at h` will tell Lean
      to reveal this for us.
      "
      simp at h
      Hint "
      We want now to deconstruct this `h` to give us
      an open set `V` which belongs to `U_col` where
      `¬V = ∅`. The tactic
      `obtain ⟨V, V_in_U_col, V_not_empty⟩ := h` does the trick.
      (To type e.g. `⟨`, use `\\<`.)
      "
      obtain ⟨V, V_in_U_col, V_not_empty⟩ := h
      Hint "
      Logically, we know that if `V` is not the empty set,
      then it must be `univ`. In Lean-speak, this means we should
      `have V_univ : V = univ := ?_`.
      "
      have V_univ : V = univ := ?_
      · Hint "
        Now we're ready to `r`e`w`rite our goal using
        `eq_univ_iff_forall`, which is a useful characterization
        for when a set equals the universe.
        "
        rw [eq_univ_iff_forall]
        Hint "
        Here we can `rintro`duce an arbitrary point
        $x\\in X$.
        "
        rintro x
        Hint "
        Lean can now `simp`lify our goal for us.
        "
        simp
        Hint "
        Finally, let's `use` the set `V`.
        "
        use V
        Hint "
        We now need to prove a conjunction of
        `V ∈ U_col` and `x ∈ V`. We can use the
        `constructor` tactic to split this into two
        subgoals.
        "
        constructor
        · Hint "
          This is `exact`ly one of our hypotheses.
          "
          exact V_in_U_col
        · Hint "
          We should `r`e`w`rite our goal to remind Lean
          what `V` is.
          "
          rw [V_univ]
          Hint "
          And Lean can handle the rest with our favorite
          four-character tactic...
          "
          simp
      Hint "
      Recall that earlier we claimed that
      `V = univ`? It's now our job to justify it.
      This is almost `U_col_open V V_in_U_col`, which says
      `V = ∅ ∨ V = univ`. So let's use
      `rcases U_col_open V V_in_U_col with V_empty|V_univ`
      to investigate each case.
      "
      rcases U_col_open V V_in_U_col with V_empty|V_univ
      · Hint "
        Wait a second! In this case, we have both
        `V_empty` and `V_not_empty`. This is `absurd`,
        and Lean will agree if we assert `exact absurd`
        along with these two contradictory hypotheses.
        "
        exact absurd V_empty V_not_empty
      · Hint "
        And this is `exact`ly our second case.
        "
        exact V_univ

Conclusion "Whew, you did it!"
