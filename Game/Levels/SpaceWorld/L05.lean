import Game.Metadata

World "SpaceWorld"
Level 5
Title "The Union Axiom"

Introduction "
Finally, we have `h.isOpen_sUnion`: the arbitrary union of open sets is open.
"

open Set Topology Nat

variable {X : Type}
/--
By definition, the union of any family of open sets is open.
-/
TheoremDoc TopologicalSpace.isOpen_sUnion as "isOpen_sUnion" in "Topology"
/--
Proof that `⋃₀ \{U, V} = U ∪ V`.
-/
TheoremDoc Set.sUnion_pair as "sUnion_pair" in "Set"
NewTheorem Set.sUnion_pair TopologicalSpace.isOpen_sUnion

NewTactic rintro

Statement (h: TopologicalSpace X) (U V : Set X) (U_open : IsOpen U)
    (V_open : IsOpen V) : IsOpen (U ∪ V) := by
  Hint "
  So of course, a finite union of open sets should be open. To convince
  Lean of this, we will need to first convert this binary union `U ∪ V` into the union
  of a set: `⋃₀ \{U, V}`.
  "
  Hint "
  The fact that `⋃₀ \{U, V} = U ∪ V` is captured by `sUnion_pair U V`, but the
  rewrite (`rw`) tactic only tries to rewrite expressions on the left side of the `=`
  with expressions on the right. This can be fixed by using `rw [← sUnion_pair U V]`.
  (To type the `←`, type `\\l` and press space.)
  "
  rw [(sUnion_pair U V).symm]
  Hint "
  Now we can apply the union axiom for topological spaces.
  "
  apply h.isOpen_sUnion
  Hint "
  Logically, we can see that we need to check two cases,
  $t=U$ and $t=V$. One way to do this in lean is the `rintro`
  tactic. Use `rintro t (rfl | rfl)` to split your goal into
  these cases.
  "
  rintro t (rfl | rfl)
  Hint "
  Here we prove the case $t=U$.
  "
  exact U_open
  Hint "
  And here we prove the case $t=V$.
  "
  exact V_open

Conclusion "Awesome job!"
