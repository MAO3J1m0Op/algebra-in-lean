import AlgebraInLean.Chapter3.Sheet1

namespace Defs
namespace Subgroups

/-
In this sheet, we build the theory of repeated application of the group operation. If the
group operation is multiplication, the functions we define in this sheet are equivalent to
exponentiation.

First, we define the power function `mpow` for monoids. Since monoids do not have a notion of
inverses, we consider only natural numbers as input.
-/
section Mpow

/--
We define this function inductively. `mpow x n` gives the element equal to multiplying the
identity element `n` times by `x`.
-/
def mpow {M : Type*} [Monoid M] (x : M) : ℕ → M
| Nat.zero => 𝕖
| Nat.succ n => μ (mpow x n) x

variable {M : Type*} [Monoid M] (x : M) (m n : ℕ)

@[simp]
theorem mpow_zero : mpow x 0 = 𝕖 := rfl

theorem mpow_succ_right : mpow x (n+1) = μ (mpow x n) x := rfl

@[simp]
theorem mpow_one : mpow x 1 = x := by
  -- EXERCISE (DIFFICULTY *)
  rw [mpow, mpow_zero, id_op]

theorem mpow_two : mpow x 2 = μ x x := by
  -- EXERCISE (*)
  rw [mpow, mpow_one]

-- Induction will prove helpful for the following exercises.
theorem mpow_succ_left : mpow x (n+1) = μ x (mpow x n) := by
  -- EXERCISE (*)
  induction n with
  | zero => rw [zero_add, mpow_one, mpow_zero, op_id]
  | succ n ih =>
    rw [mpow_succ_right]
    nth_rw 2 [mpow_succ_right]
    rw [ih, op_assoc]

theorem mpow_add : μ (mpow x m) (mpow x n) = mpow x (m + n) := by
  -- EXERCISE (*)
  induction n with
  | zero => rw [mpow_zero, op_id, Nat.add_zero]
  | succ n ih =>
    rw [←Nat.add_assoc, mpow_succ_right, mpow_succ_right, ←op_assoc, ih]

theorem mpow_mul : mpow x (m * n) = mpow (mpow x m) n := by
  -- EXERCISE (*)
  induction n with
  | zero =>
    rw [mul_zero, mpow_zero, mpow_zero]
  | succ n ih =>
    simp_rw [Nat.mul_succ, ←mpow_add, ih, mpow_one]
  done

@[simp]
theorem mpow_id : mpow 𝕖 n = (𝕖 : M) := by
  -- EXERCISE (*)
  induction n with
  | zero => rfl
  | succ n ih => rw [mpow_succ_right, ih, op_id]
  done

end Mpow

section Gpow

/--
Now, we define the power function for groups. Since groups have inverses, there becomes a natural
notion of negative exponentiation. Notice that `Int` has two constructors.
-/
def gpow {G : Type*} [Group G] (x : G) : ℤ → G
/- `Int.ofNat` covers the positive end of the integers. -/
| Int.ofNat n => mpow x n
/-
Since the integer zero is already covered by `Int.ofNat 0`, it is not helpful for the negative
constructor to have its own notion of zero. Instead, the negative constructor offsets the provided
natural number by one before negating it. So, (0 : ℕ) maps to (-1 : ℤ), (1 : ℕ) maps to (-2 : ℤ),
and so on. Keep this in mind as you work with `gpow`.
-/
| Int.negSucc n => ι (μ (mpow x n) x)

variable {G : Type*} [Group G] (x : G)

lemma gpow_ofNat (n : ℕ) : gpow x ↑n = mpow x n := rfl

lemma gpow_negSucc (n : ℕ) : gpow x (Int.negSucc n) = ι (μ (mpow x n) x) := rfl

@[simp]
lemma gpow_zero : gpow x 0 = 𝕖 := rfl

@[simp]
lemma gpow_one : gpow x 1 = x := by
  -- EXERCISE (*)
  rw [←Int.ofNat_one, gpow_ofNat, mpow_one]

lemma gpow_two : gpow x 2 = μ x x := by
  -- EXERCISE (*)
  rw [←Int.ofNat_two, gpow_ofNat, mpow_two]

/-
Going between integers and natural numbers requires precision, and can be difficult at times.
Consult the documentation on `Int` if you're running into trouble.
-/

lemma gpow_neg_mpow (n : ℕ) : gpow x (-n) = ι (mpow x n) := by
  -- EXERCISE (**)
  cases n with
  | zero =>
    rw [Int.ofNat_zero, Int.neg_zero, gpow_zero, mpow_zero, inv_id]
  | succ n =>
    have : -↑(n + 1) = Int.negSucc n := rfl
    rw [this, gpow_negSucc, ←mpow_succ_right, mpow_succ_left]

@[simp]
lemma gpow_neg_one : gpow x (-1) = ι x := by
  -- EXERCISE (*)
  rw [←Int.ofNat_one, gpow_neg_mpow, mpow_one]

lemma gpow_neg (n : ℤ) : gpow x (-n) = ι (gpow x n) := by
  -- EXERCISE (**)
  induction n using Int.induction_on with
  | hz => simp [inv_id]
  | hp n ih =>
    rw [←Int.cast_one]
    sorry
  | hn n ih => sorry

@[simp]
-- EXERCISE (**)
lemma gpow_succ (n : ℤ) : gpow x (n + 1) = μ (gpow x n) x := by
  induction n using Int.induction_on with
  | hz => rfl
  | hp n _ =>
    repeat rw [←Int.ofNat_one]
    repeat rw [Int.ofNat_add_out]
    repeat rw [gpow_ofNat]
    rfl
  | hn n _ =>
    sorry

lemma gpow_pred (n : ℤ) : μ (gpow x n) (ι x) = gpow x (n-1) := by
  -- EXERCISE (**)
  induction n using Int.induction_on with
  | hz => simp only [gpow_zero, id_op, zero_sub, gpow_neg_one]
  | hp n _ =>
    rw [gpow_succ, gpow_ofNat, op_assoc, op_inv, op_id]
    rw [add_sub_cancel_right, gpow_ofNat]
  | hn n _ =>
    sorry

@[simp]
lemma gpow_add (m n : ℤ) : μ (gpow x m) (gpow x n) = gpow x (m + n) := by
  -- EXERCISE (**)
  sorry

@[simp]
lemma gpow_sub (m n : ℤ) : μ (gpow x m) (ι (gpow x n)) = gpow x (m - n) := by
  -- EXERCISE (*)
  rw [sub_eq_add_neg, ←gpow_add, gpow_neg]

@[simp]
lemma gpow_mul (m n : ℤ) : gpow x (m * n) = gpow (gpow x m) n := by
  -- EXERCISE (???)
  sorry

/--
The first thing pertaining to subgroups we will prove about `gpow` is that all subgroups are closed
under the function.
-/
theorem gpow_closure {H : Subgroup G} {n : ℤ} : x ∈ H → gpow x n ∈ H := by
  -- EXERCISE (*)
  intro h
  induction n using Int.induction_on with
  | hz => exact H.has_id
  | hp n ih =>
    rw [gpow_succ]
    apply H.mul_closure
    · exact ih
    · exact h
  | hn n ih =>
    rw [←gpow_pred, gpow_neg]
    apply H.mul_closure
    · rw [←gpow_neg]
      exact ih
    · apply H.inv_closure
      exact h
  done

end Gpow
end Subgroups
end Defs
