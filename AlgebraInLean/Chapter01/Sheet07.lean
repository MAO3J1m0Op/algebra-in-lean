import AlgebraInLean.Chapter01.Sheet06

namespace AlgebraInLean

set_option linter.unusedTactic false

/-
The last group we will cover in this section is the symmetric group. This is defined as the set of
all permutations of a set of n elements. This is formalized as the set of all bijections of a finite
set of size n onto itself. The group operation, therefore, is function composition.

For example, S3 has 6 elements, which permute the tuple (1, 2, 3) into one of: (1, 2, 3), (1, 3, 2),
(2, 1, 3), (2, 3, 1), (3, 1, 2), or (3, 2, 1).

In Lean, we use the `Equiv` type, notated `α ≃ β`, which is the set of all bijections from a type
`α` to a type `β`.
-/

def Symmetric (n : ℕ) : Type := Fin n ≃ Fin n

instance (n : ℕ) : Group (Symmetric n) where
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
