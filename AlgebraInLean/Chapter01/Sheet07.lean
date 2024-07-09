import AlgebraInLean.Chapter01.Sheet06

namespace AlgebraInLean

/-
The last group we will cover in this section is the symmetric group. This is defined as the set of
all permutatins of a set of n elements. This is formalized as the set of all bijections of a finite
set of size n onto itself. The group operation, therefore, is function composition.

For example, S3 has 6 elements, which permute the tuple (1, 2, 3) into one of: (1, 2, 3), (1, 3, 2),
(2, 1, 3), (2, 3, 1), (3, 1, 2), or (3, 2, 1).

In Lean, we use the `Equiv` type, notated `α ≃ β`, which is the set of all bijections from a type
`α` to a type `β`.
-/
def Sn (n : ℕ) : Type := Fin n ≃ Fin n

instance (n : ℕ) : Group (Sn n) where
  op := Equiv.trans
  op_assoc := λ _ _ _ ↦ rfl
  id := Equiv.refl (Fin n)
  op_id := λ _ ↦ rfl
  id_op := λ _ ↦ rfl
  inv := Equiv.symm
  inv_op := by
    intro f
    dsimp [μ, 𝕖]
    rw [←Equiv.coe_inj]
    funext x
    rw [Equiv.symm_trans_self, Equiv.refl_apply]
    done

/--
This is a type similar in structure to `Fin 3`, but is easier to work with for the proof below.
-/
inductive Three where
| one   : Three
| two   : Three
| three : Three
/-
The line below enables the use of the `decide` tactic for closing goals involving the equality (or
inequality) of our `Three` type.
-/
deriving DecidableEq

/-
Here, we construct a bijection between our custom `Three` type and `Fin 3`.
-/
def three_eq : Three ≃ Fin 3 where
  toFun x := match x with
  | Three.one => 0
  | Three.two => 1
  | Three.three => 2
  invFun x := match x with
  | 0 => Three.one
  | 1 => Three.two
  | 2 => Three.three
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    dsimp only
    split <;> case _ heq =>
      split at heq
      all_goals (first | rfl | contradiction)

open Three in
theorem S3_non_abelian : ¬∀ (f g : Three ≃ Three), f.trans g = g.trans f := by

  /-
  Recall that the classical way to disprove a for-all statement is to construct a counterexample.
  Here, we will guide you through the construction of a counterexample.

  Fill in the `sorry`s to construct specific functions that demonstrate that S3 is non-abelian.
  -/
  let f : Three → Three := λ x ↦ match x with
  | one   => one
  | two   => three
  | three => two
  let f_inv : Three → Three := λ x ↦ match x with
  | one   => one
  | two   => three
  | three => two

  let g : Three → Three := λ x ↦ match x with
  | one   => two
  | two   => one
  | three => three
  let g_inv : Three → Three := λ x ↦ match x with
  | one   => two
  | two   => one
  | three => three

  /-
  The next two blocks construct `Equiv` instances from the four functions you constructed above.

  Don't worry about the `sorry` declarations here; they're just there as fallback for Lean before
  you have completed the function calls above.
  -/
  let f_eq : Three ≃ Three := {
    toFun := f
    invFun := f_inv
    left_inv := by
      intro x
      dsimp [f, f_inv]
      split <;> case _ heq =>
        split at heq
        all_goals (first | rfl | contradiction | sorry)
    right_inv := by
      intro x
      dsimp [f, f_inv]
      split <;> case _ heq =>
        split at heq
        all_goals (first | rfl | contradiction | sorry)
  }

  let g_eq : Three ≃ Three := {
    toFun := g
    invFun := g_inv
    left_inv := by
      intro x
      dsimp [g, g_inv]
      split <;> case _ heq =>
        split at heq
        all_goals (first | rfl | contradiction | sorry)
    right_inv := by
      intro x
      dsimp [g, g_inv]
      split <;> case _ heq =>
        split at heq
        all_goals (first | rfl | contradiction | sorry)
  }

  /-
  Here, we extract all the definitons, and convert the negated ∀ into a ∃ counterexample. The goal
  state after this block will look rather heinous, but trust that it has been placed in a format
  that will allow Lean to cleanly close the goal (by way of the `decide` tactic) once you pick a
  specific point of failure for the equality.
  -/
  apply not_forall_of_exists_not
  use f_eq
  apply not_forall_of_exists_not
  use g_eq
  rw [←Equiv.coe_inj]
  simp [f_eq, f, g_eq, g, Eq.trans, Function.comp_apply]
  rw [Function.funext_iff]
  apply not_forall_of_exists_not

  /-
  Finally, pick a specific function value where the equality fails with the `use` tactic, and then
  use the `decide` tactic to close the goal!

  Before you move on, though, check that the `sorry` warning has disappeared from this lemma. If
  it's still there, double check your functions, as that means the `Equiv` creation blocks are
  failing because the functions you constructed are not bijective.
  -/

  -- EXERCISE
  use three
  decide
