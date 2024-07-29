import AlgebraInLean.Chapter03.Sheet01

namespace AlgebraInLean

set_option linter.unusedTactic false

/-
## Challenge Sheet

In this sheet, we build the theory of repeated application of the group operation. If the group
operation is multiplication, the functions we define in this sheet are equivalent to exponentiation.

First, we define the power function `mpow` for monoids. Let M be a Monoid and x ∈ M. Since monoids
do not have a notion of inverses, we only define xⁿ for n ∈ ℕ.
-/
section Mpow

/--
We define this function inductively. `mpow x n` gives the element equal to multiplying the
identity element `n` times by `x`.
-/
def mpow {M : Type*} [Monoid M] (x : M) : ℕ → M
| Nat.zero => 𝕖   -- m⁰ = 𝕖
| Nat.succ n => μ (mpow x n) x  -- m ^ (n + 1) = m * m ^ n

variable {M : Type*} [Monoid M] (x : M) (m n : ℕ)

-- These are true by definition
@[simp]
lemma mpow_zero : mpow x 0 = 𝕖 := rfl

@[simp]
lemma mpow_succ_right : mpow x (n+1) = μ (mpow x n) x := rfl

/-- x¹ = x -/
@[simp]
lemma mpow_one : mpow x 1 = x := by
  -- EXERCISE (DIFFICULTY *)
  rw [mpow, mpow_zero, id_op]

/-- x² = x * x -/
lemma mpow_two : mpow x 2 = μ x x := by
  -- EXERCISE (*)
  rw [mpow, mpow_one]

-- Induction will prove helpful for the following exercises.

/-- x ^ (n + 1) = x * x ^ n-/
lemma mpow_succ_left : mpow x (n+1) = μ x (mpow x n) := by
  -- EXERCISE (*)
  induction n with
  | zero => rw [zero_add, mpow_one, mpow_zero, op_id]
  | succ n ih =>
    rw [mpow_succ_right]
    nth_rw 2 [mpow_succ_right]
    rw [ih, op_assoc]

/--  x ^ (m + n) = x ^ m * x ^ n -/
lemma mpow_add : mpow x (m + n) = μ (mpow x m) (mpow x n) := by
  -- EXERCISE (*)
  induction n with
  | zero => rw [mpow_zero, op_id, Nat.add_zero]
  | succ n ih =>
    rw [←Nat.add_assoc, mpow_succ_right, mpow_succ_right, ←op_assoc, ih]

/-- x ^ (m * n) = (x ^ m) ^ n-/
lemma mpow_mul : mpow x (m * n) = mpow (mpow x m) n := by
  -- EXERCISE (*)
  induction n with
  | zero =>
    rw [mul_zero, mpow_zero, mpow_zero]
  | succ n ih =>
    simp_rw [Nat.mul_succ, mpow_add, ih, mpow_one]
  done

/-- e ^ n = e -/
@[simp]
lemma mpow_id : mpow 𝕖 n = (𝕖 : M) := by
  -- EXERCISE (*)
  induction n with
  | zero => rfl
  | succ n ih => rw [mpow_succ_right, ih, op_id]
  done

lemma mpow_comm_self : μ (mpow x n) x = μ x (mpow x n) := by
  induction n with
  | zero => rw [mpow_zero, op_id, id_op]
  | succ n ih =>
    nth_rw 1 [mpow_succ_left, mpow_succ_right]
    rw [op_assoc, ih]
  done

lemma mpow_comm_mpow : μ (mpow x n) (mpow x m) = μ (mpow x m) (mpow x n) := by
  induction n with
  | zero => rw [mpow_zero, op_id, id_op]
  | succ n ih =>
    rw [mpow_succ_left, op_assoc, ih]
    nth_rw 2 [←op_assoc]
    rw [mpow_comm_self, op_assoc]
  done

end Mpow

/-
This concludes our theory of monoid powers. Are there any other properties you think monoid
powers should have? Try to state and prove them!
-/

section Gpow

/--
Now, we define the power function for groups. Since groups have inverses, there becomes a natural
notion of negative exponentiation. Notice that `Int` has two constructors of type `Nat → Int`.
-/
def gpow {G : Type*} [Group G] (x : G) : ℤ → G
/- The integer type can be constructed using natural numbers. This is done through an inductive type
with two constructors, indicating the two possible states of an integer (those being negative and
nonnegative). The constructor `Int.ofNat` covers the nonnegative end of the integers (those that are
equivalent to a `Nat`, hence the name `ofNat`). -/
| Int.ofNat n => mpow x n
/-
Since the integer zero is already covered by `Int.ofNat 0`, it is not helpful for the negative
constructor to have its own notion of zero. Instead, the negative constructor offsets the provided
natural number by one before negating it. So, (0 : ℕ) maps to (-1 : ℤ), (1 : ℕ) maps to (-2 : ℤ),
and so on. This warrants the name `negSucc`, as in "the negation of the successor of the inputted
natural number". Keep this in mind as you work with `gpow`.
-/
| Int.negSucc n => mpow (ι x) (n+1)

variable {G : Type*} [Group G] (x : G)

lemma gpow_ofNat (n : ℕ) : gpow x ↑n = mpow x n := rfl

lemma gpow_negSucc (n : ℕ) : gpow x (Int.negSucc n) = mpow (ι x) (n+1) := rfl

lemma inv_mpow (n : ℕ) : ι (mpow x n) = mpow (ι x) n := by
  induction n with
  | zero =>
    simp_rw [mpow_zero]
    exact inv_id
  | succ n ih =>
    simp_rw [mpow_add, inv_anticomm, ih, mpow_one, mpow_comm_self]
  done

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
    rw [this, gpow_negSucc, inv_mpow]

@[simp]
lemma gpow_neg_one : gpow x (-1) = ι x := by
  -- EXERCISE (*)
  rw [←Int.ofNat_one, gpow_neg_mpow, mpow_one]

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
    rw [←Int.negSucc_coe', gpow_negSucc, mpow_succ_right, op_assoc, inv_op, op_id]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right, gpow_neg_mpow]
    exact inv_mpow x n

lemma gpow_pred {n : ℤ} : μ (gpow x n) (ι x) = gpow x (n - 1) := by
  induction n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe]
    cases n with
    | zero =>
      simp only [CharP.cast_eq_zero, gpow_zero, id_op, zero_sub, Int.reduceNeg, gpow_neg_one]
    | succ n =>
      simp only [gpow, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [mpow_add, mpow_one, op_assoc, op_inv, op_id]
  | negSucc n =>
    dsimp only [gpow, Int.negSucc_sub_one]
    rw [←mpow_succ_right]
  done

lemma gpow_add {m n : ℤ} : μ (gpow x m) (gpow x n) = gpow x (m + n) := by
  -- EXERCISE (*)
  -- Adapted from Mathlib (see the proof of `zpow_add`).
  induction n using Int.induction_on with
  | hz => rw [add_zero, gpow_zero, op_id]
  | hp n ihn =>
      simp only [←Int.add_assoc, gpow_succ, op_assoc]
      rw [←ihn]
      repeat rw [←op_assoc]
  | hn n ihn =>
    rw [←gpow_pred, ←op_assoc, ihn, gpow_pred, Int.add_sub_assoc]
  done

lemma gpow_neg (n : ℤ) : gpow x (-n) = ι (gpow x n) := by
  -- EXERCISE (**)
  induction n using Int.induction_on with
  | hz => rw [neg_zero, gpow_zero, inv_id]
  | hp n ih =>
    rw [Int.neg_add, ←Int.sub_eq_add_neg, ←gpow_pred, ih, ←inv_anticomm, add_comm]
    rw [←gpow_add, gpow_one]
  | hn n ih =>
    simp at *
    rw [add_comm, gpow_succ, ih, ←gpow_pred, gpow_neg_mpow, inv_anticomm]
    repeat rw [inv_inv]
    rw [←mpow_succ_right, mpow_succ_left]

  done

@[simp]
lemma gpow_sub (m n : ℤ) : μ (gpow x m) (ι (gpow x n)) = gpow x (m - n) := by
  -- EXERCISE (*)
  rw [sub_eq_add_neg, ←gpow_add, gpow_neg]


lemma gpow_mul (m n : ℤ) : gpow x (m * n) = gpow (gpow x m) n := by
  -- EXERCISE (*)
  induction n using Int.induction_on with
  | hz => rw [mul_zero, gpow_zero, gpow_zero]
  | hp n ih => rw [mul_add, mul_one, ←gpow_add, gpow_succ, ih]
  | hn n ih => rw [Int.mul_sub, mul_one, ←gpow_sub, ←gpow_pred, ih]

-- The first thing we will prove about `gpow` is that subgroups are closed under the function.
theorem gpow_closure {H : Subgroup G} {n : ℤ}: x ∈ H → gpow x n ∈ H := by
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
