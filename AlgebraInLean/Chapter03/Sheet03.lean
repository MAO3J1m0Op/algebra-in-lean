import AlgebraInLean.Chapter03.Sheet02

namespace AlgebraInLean

set_option linter.unusedTactic false

section MonoidOrder

/-
## Challenge Sheet

Let M be a monoid, and let x : M. The order of x is the smallest nonzero natural number n such that
xⁿ = e if such an n exists. Otherwise, the order of x is defined to be 0. How would you implement
this definition in Lean?

A starting point would be to consider the proposition
-/

def isFiniteOrder {M : Type*} [Monoid M] (x : M): Prop := ∃ (n : ℕ), n ≠ 0 ∧ mpow x n = 𝕖

/-
If this proposition is true, we can access the value of n that yields xⁿ = e. But we do not simply
want any `n : ℕ` that satisfies mpow x n = 𝕖, we want the smallest! After a quick search of the Nat
namespace in mathlib, there appears to be a function `Nat.find`, that takes in a proposition `h` and
returns the smallest natural number that satisfies `h`.

Then, we could use an if statement to define `order`: if `h : isFiniteOrder x`, then `order x` is
`Nat.find h`. Else, `order x` should be 0.

Try uncommenting the following lines to see if this idea works:

def order {M : Type*} [Monoid M] (x : M) : ℕ := if h : isFiniteOrder x then Nat.find h else 0

The issue is subtle.

The definition above asserts that `if h : isFiniteOrder x then Nat.find h else 0` has type `ℕ`.
However, when Lean type-checks this definition, it doesn't know whether the proposition
`isFiniteOrder x` is true or false, and so it can't decide what the type of the entire if-block
above is either.

You may object to this: if `isFiniteOrder x` is true, then the expression is the natural number
returned by Nat.find and if `isFiniteOrder x` is false, then the expression is the natural number 0.
In either case, the expression has type `ℕ`. Shouldn't Lean be able to figure this out?

Implicit in this intuition is the idea that every proposition is either true or false, even if we
don't necessarily have a way to compute the result. In other words, for any proposition `p`, either
`p` is true or its negation `¬p` is true. However, this seemingly trivial claim, called the Law of
the Excluded Middle, is not always true in constructive mathematics! Moreover, Lean's foundations for
proving theorems is constructive: if you want to prove a proposition `p`, you have to construct a
term that has type p (i.e., a term of type `p` is a proof of `p`).

Meanwhile, classical logic asserts the Law of Excluded Middle as an axiom. In Lean, the story is complicated.
Since Lean is a programming language it must be capable of producing a program that can be
evaulated by a computer. So if we were to write a function including the snippet below, where `p` is
an arbitrary `Prop`:

```
if p then 1 else 0
```

then what if `p` is equal to a proposition not yet proven in Lean? The code snippet would be
impossible to evaluate. However, if this computability requirement is not needed, and a definition
is only meant to be reasoned about in theorems, Lean has the `noncomputable` keyword for such cases.
For example, in the definition below, Lean cannot compute for an arbitrary monoid whether there is
some nonzero power that yields the identity, so we are required to use the classical law of excluded
middle (utilized through the `classical`) keyword to construct the definition.

For further reading, consult the documentation on the below definitions:

* `Decidable` type class (Init.Prelude)
* `Classical` namespace
-/
noncomputable def order {M : Type*} [Monoid M] (x : M) : ℕ := by
  classical exact if h : isFiniteOrder x then Nat.find h else 0

variable {M : Type*} [Monoid M] (x : M) (m n : ℕ)

/-
If a tactic fails with an error pertaining to failure to synthesize instance of `Decidable`,
`DecidablePred`, or other type classes belonging to the decidable family, prefixing the failing
tactic with the `classical` tactic should remove these errors. `classical` works by running the
tactics in scope where all propositions are decidable (i.e., every proposition is an isntance of the
type-class Classical.propDecidable). Keep this in mind for this and future exercises. Similarly, you
may find `split_ifs` and `Nat.find_spec` to be helpful tactics.
-/

/-- If xⁿ = e → n = 0 -/
lemma mpow_order_zero (h₀ : order x = 0) : mpow x n = 𝕖 → n = 0 := by
  -- EXERCISE (*.5)
  intro hn
  dsimp [order] at h₀
  split_ifs at h₀ with h
  · absurd h₀
    classical have hFinite : ¬(Nat.find h) = 0 ∧ mpow x (Nat.find h) = 𝕖 := Nat.find_spec h
    exact hFinite.left
  · contrapose! h
    use n

/-- If n is the order of x, then xⁿ = e -/
lemma mpow_order : mpow x (order x) = 𝕖 := by
  -- EXERCISE (*.5)
  set n := order x with hn
  dsimp [order] at hn
  split_ifs at hn with h <;> rw [hn]
  · classical exact (Nat.find_spec h).right
  · rfl
  done

/-- Let m be the order x. Write m = nq + r with 0 ≤ r < m. Then, xʳ = xⁿ  -/
lemma mpow_mod_order : mpow x (m % order x) = mpow x m := by
  -- EXERCISE (*)
  set n := order x
  nth_rw 2 [←Nat.mod_add_div m n]
  rw [mpow_add, mpow_mul, mpow_order, mpow_id, op_id]
  done

/-- Let n be the order of x. xᵐ = e ↔ n | m -/
lemma order_divides_iff_mpow_id : mpow x m = 𝕖 ↔ order x ∣ m := by
  apply Iff.intro
  · intro hm
    by_cases hm0 : m = 0
    · -- EXERCISE (*)
      use 0
      rw [mul_zero, hm0]
    · -- EXERCISE (***)
      set n := order x with hn
      dsimp [order] at hn
      split_ifs at hn with h
      · by_contra hnm
        have : m % n < n
        · apply Nat.mod_lt
          rw [hn, GT.gt, pos_iff_ne_zero]
          classical exact (Nat.find_spec h).left
        · nth_rw 2 [hn] at this
          classical apply Nat.find_min h this
          apply And.intro
          · rw [ne_eq, ←Nat.dvd_iff_mod_eq_zero n m]
            exact hnm
          · rw [mpow_mod_order, hm]
      · exfalso
        apply h
        use m
  · -- EXERCISE (*)
    rintro ⟨k, rfl⟩
    rw [mpow_mul, mpow_order, mpow_id]
  done

/-- The order of x is nonzero if and only if there exists an n : ℕ such that xⁿ = e -/
lemma order_nonzero_iff : order x ≠ 0 ↔ ∃ n ≠ 0, mpow x n = 𝕖 := by
  apply Iff.intro
  · intro h
    use order x
    apply And.intro h
    exact mpow_order x
  · intro ⟨n, hn⟩
    by_contra! h₀
    absurd hn.left
    rw [←Nat.zero_dvd, ←h₀, ←order_divides_iff_mpow_id]
    exact hn.right

/-- The order of the identity element, 𝕖, in any monoid is 1. -/
lemma order_id : order (𝕖 : M) = 1 := by
  unfold order
  split
  · case _ h =>
    unfold isFiniteOrder at h
    classical rw [Nat.find_eq_iff]
    apply And.intro
    · apply And.intro
      · exact Nat.one_ne_zero
      · exact mpow_id 1
    · intro n hn
      rw [and_iff_not_or_not, not_not]
      left
      push_neg
      exact Nat.lt_one_iff.mp hn
  · case _ h =>
    absurd h
    use 1
    apply And.intro
    · exact Nat.one_ne_zero
    · exact mpow_id 1

/-- Let m be the order of x and let n : ℕ with n ≠ 0. If m ≠ 0, then the order of xⁿ is nonzero -/
lemma mpow_nonzero_order (n : ℕ) (h : order x ≠ 0) : order (mpow x n) ≠ 0 := by
  obtain ⟨m, hm⟩ := (order_nonzero_iff x).mp h
  suffices : ∃ k ≠ 0, mpow (mpow x n) k = 𝕖
  · rw [order_nonzero_iff]
    exact this
  use m
  apply And.intro
  · exact hm.left
  · rw [←mpow_mul, mul_comm, mpow_mul, hm.right, mpow_id]

/-
In any monoid, if the order of x is nonzero, then there is an element y that serves as both a left
and right inverse to x.
-/
lemma inverse_of_nonzero_order (h : order x ≠ 0) : ∃ (y : M), μ x y = 𝕖 ∧ μ y x = 𝕖 := by
  use mpow x (order x - 1)
  apply And.intro
  · nth_rw 1 [←mpow_one x]
    rw [←mpow_add, add_comm]
    rw [Nat.sub_add_cancel]
    · exact mpow_order x
    · exact Nat.one_le_iff_ne_zero.mpr h
  · nth_rw 3 [←mpow_one x]
    rw [←mpow_add]
    rw [Nat.sub_add_cancel]
    · exact mpow_order x
    · exact Nat.one_le_iff_ne_zero.mpr h

/-- Suppose m, n < `order x`. If xᵐ = xⁿ, then m = n -/
lemma mpow_inj_of_lt_order (hm : m < order x) (hn : n < order x)
  : mpow x m = mpow x n → m = n := by
  -- EXERCISE (**)
  intro h
  wlog hmn : m ≤ n
  · symm
    exact this x n m hn hm (Eq.symm h) (Nat.le_of_not_ge hmn)
  obtain ⟨k, hk⟩ := Nat.le.dest hmn
  suffices : k = 0
  · rw [this, add_zero] at hk
    exact hk
  apply Nat.eq_zero_of_dvd_of_lt
  · rw [←order_divides_iff_mpow_id x]
    have op_cancel_left : ∀ u v : M, μ (mpow x m) u = μ (mpow x m) v → u = v
    · intro u v heq
      rw [←id_op u, ←id_op v]
      have : ∃ (x' : M), μ x' (mpow x m) = 𝕖
      · have : order x ≠ 0 := by linarith
        by_cases hm' : m = 0
        · use 𝕖
          rw [id_op, hm', mpow_zero]
        · have this := mpow_nonzero_order x m this
          obtain ⟨x', hx'⟩ := inverse_of_nonzero_order (mpow x m) this
          use x'
          exact hx'.right
      obtain ⟨x', op_inv⟩ := this
      repeat rw [←op_inv]
      repeat rw [op_assoc]
      congr
    apply op_cancel_left
    rw [op_id, ←mpow_add, hk]
    exact Eq.symm h
  · rw [←hk] at hn
    linarith
  done

/-- Let r ≠ 0 be the order of x. If xᵐ = xⁿ, then m is congruent to n (mod r) -/
lemma mod_order_eq_of_mpow_eq (h : order x ≠ 0)
  -- EXERCISE (*)
  : mpow x m = mpow x n → m % (order x) = n % (order x) := by
  intro heq
  apply mpow_inj_of_lt_order x (m % order x) (n % order x)
  · apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero h
  · apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero h
  · repeat rw [mpow_mod_order]
    exact heq
  done

end MonoidOrder

section GroupOrder

variable {G : Type*} [Group G] (x : G)

/-- Let n be the order x. Then, xⁿ = 𝕖 -/
lemma gpow_order : gpow x (order x) = 𝕖 := by
  rw [gpow_ofNat, mpow_order]

/- For any integer n, 𝕖ⁿ = 𝕖, if 𝕖 is the identity of a group G. -/
lemma gpow_id (n : ℤ) : gpow (𝕖 : G) n = 𝕖 := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, gpow_ofNat, mpow_id]
  | negSucc n =>
    rw [gpow_negSucc, mpow_succ_right, inv_id, op_id, mpow_id]

/-- Suppose the order of x is 0. Then if xⁿ = 𝕖, n = 0 -/
lemma gpow_order_zero {n : ℤ} (h₀ : order x = 0) : gpow x n = 𝕖 → n = 0 := by
  intro h
  cases n with
  | ofNat n =>
    -- EXERCISE (*)
    congr
    exact mpow_order_zero x n h₀ h
  | negSucc n =>
    -- EXERCISE (**)
    exfalso
    absurd h₀
    push_neg
    rw [order_nonzero_iff]
    use n + 1
    apply And.intro
    · exact Ne.symm (Nat.zero_ne_add_one n)
    · apply inv_inj
      rw [inv_id, inv_mpow]
      exact h

/-- Let m be the order x. Write m = nq + r with 0 ≤ r < m. Then, xʳ = xⁿ  -/
lemma gpow_mod_order {n : ℤ} : gpow x (n % order x) = gpow x n := by
  -- EXERCISE (**)
  cases n with
  | ofNat n =>
    have : (n : ℤ) % (↑(order x)) = (n % order x : ℕ) := rfl
    rw [Int.ofNat_eq_coe, this, gpow_ofNat, gpow_ofNat, mpow_mod_order]
  | negSucc n =>
    nth_rw 2 [←Int.emod_add_ediv (Int.negSucc n) (order x)]
    rw [←gpow_add, gpow_mul, gpow_order, gpow_id, op_id]
  done

/-- Suppose the order of x is 0. Then xᵐ = xⁿ → m = n-/
lemma gpow_inj_of_order_zero {m n : ℤ} (h : order x = 0) (heq : gpow x m = gpow x n) : m = n := by
  induction n using Int.induction_on generalizing m with
  | hz =>
    apply gpow_order_zero x h
    exact heq
  | hp n ih =>
    rw [←Int.sub_add_cancel m 1]
    congr 1
    apply ih
    rw [←gpow_pred, heq, gpow_succ, op_assoc, op_inv, op_id]
  | hn n ih =>
    rw [←Int.add_sub_cancel m 1]
    congr 1
    apply ih
    rw [gpow_succ, heq, ←gpow_pred, op_assoc, inv_op, op_id]

/-
This lemma has nothing to do with `order`, but is essential to the following theorem.
If `m` is a positive integer, then every integer is congruent [MOD m] to some natural number.
-/
lemma emod_has_nat {m : ℕ} (n : ℤ) (hm : 0 < m) : ∃ (n' : ℕ), n % m = n' % m := by
  cases n with
  | ofNat n =>
    use n
    rfl
  | negSucc n =>
    use m - 1 - n % m
    rw [Int.natCast_sub, Int.natCast_sub]
    · rw [Int.ofNat_emod n m, Nat.cast_one]
      rw [←@Int.negSucc_emod n m]
      symm
      apply Int.emod_emod
      rw [Int.ofNat_pos]
      exact hm
    · exact hm
    · apply Nat.le_sub_one_of_lt
      apply Nat.mod_lt
      exact hm

/--
The capstone theorem of `gpow`: let r = order x. Then if two integers `m` and `n` satisfy xᵐ = xⁿ,
then m ≡ n [MOD order x]. If r = 0, then m = n.
-/
lemma mod_order_eq_of_gpow_eq {m n : ℤ}
  : gpow x m = gpow x n → m % (order x) = n % (order x) := by
  intro h
  by_cases h₀ : order x = 0
  · rw [h₀]
    simp
    exact gpow_inj_of_order_zero x h₀ h
  · obtain ⟨m', hm'⟩ := emod_has_nat m (Nat.zero_lt_of_ne_zero h₀)
    obtain ⟨n', hn'⟩ := emod_has_nat n (Nat.zero_lt_of_ne_zero h₀)
    rw [hm', hn']
    repeat rw [←Int.ofNat_emod]
    congr 1
    apply mod_order_eq_of_mpow_eq x m' n' h₀
    rw [←mpow_mod_order x m', ←mpow_mod_order x n']
    repeat rw [←gpow_ofNat, Int.ofNat_emod]
    rw [←hm', ←hn']
    repeat rw [gpow_mod_order]
    exact h

end GroupOrder
