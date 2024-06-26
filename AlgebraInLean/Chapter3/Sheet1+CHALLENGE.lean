import «AlgebraInLean».Chapter3.Sheet1

namespace Defs
  namespace Subgroups

    def mpow [Monoid M] (x : M) : ℕ → M
    | Nat.zero => 𝕖
    | Nat.succ n => μ (mpow x n) x

    @[simp]
    theorem mpow_zero [Monoid M] (x : M) : mpow x 0 = 𝕖 := rfl

    @[simp]
    theorem mpow_one [Monoid M] (x : M) : mpow x 1 = x := by
      rw [mpow, mpow_zero, id_op]

    theorem mpow_two [Monoid M] (x : M) : mpow x 2 = μ x x := by
      rw [mpow, mpow_one]

    @[simp]
    theorem mpow_succ [Monoid M] (x : M) (n : ℕ) : mpow x (n+1) = μ (mpow x n) x := rfl

    @[simp]
    theorem mpow_add [Monoid M] (x : M) (m n : ℕ) : μ (mpow x m) (mpow x n) = mpow x (m + n) := by
      induction n with
      | zero => rw [mpow_zero, op_id, Nat.add_zero]
      | succ n ih =>
        rw [←Nat.add_assoc, mpow_succ, mpow_succ, ←op_assoc, ih]
  end Subgroups
end Defs
