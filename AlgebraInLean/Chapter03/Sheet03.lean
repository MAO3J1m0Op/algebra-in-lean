import AlgebraInLean.Chapter03.Sheet02

namespace AlgebraInLean
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
the Excluded Middle, is not true in constructive mathematics! Moreover, Lean's foundations for
proving theorems is constructive: if you want to prove a proposition `p`, you have to construct a
term that has type p (i.e., a term of type `p` is a proof of `p`). What we need is classical logic!

[TODO: Unsatisfactory transition]

Classical logic asserts the Law of Excluded Middle as an axiom. In Lean, the story is complicated.
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
`DecidablePred`, or other type classes belonging to the decidable family, prefixing the
failing tactic with the `classical` tactic should remove these errors. It does so by using
noncomputable instances of these type classes implemented on all `Prop`s. Keep this in mind
for this and future exercises. Similarly, you may find `split_ifs` to be a helpful tactic.
-/

theorem mpow_order_zero (h₀ : order x = 0) : mpow x n = 𝕖 → n = 0 := by
  -- EXERCISE (*.5)
  intro hn
  dsimp [order] at h₀
  split_ifs at h₀ with h
  · absurd h₀
    classical have : ¬(Nat.find h) = 0 ∧ mpow x (Nat.find h) = 𝕖 := Nat.find_spec h
    exact this.left
  · contrapose! h
    use n

theorem mpow_order : mpow x (order x) = 𝕖 := by
  -- EXERCISE (*.5)
  set n := order x with hn
  dsimp [order] at hn
  split_ifs at hn with h <;> rw [hn]
  · classical exact (Nat.find_spec h).right
  · rfl
  done

theorem order_nonzero (h : order x ≠ 0) : ∃ n ≠ 0, mpow x n = 𝕖 := by
  use order x
  apply And.intro h
  exact mpow_order x

theorem mpow_mod_order : mpow x (m % order x) = mpow x m := by
  -- EXERCISE (*)
  set n := order x
  nth_rw 2 [←Nat.mod_add_div m n]
  rw [mpow_add, mpow_mul, mpow_order, mpow_id, op_id]
  done

theorem order_divides_iff_mpow_id : mpow x m = 𝕖 ↔ order x ∣ m := by
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
          · rw [←Nat.dvd_iff_mod_eq_zero]
            exact hnm
          · rw [mpow_mod_order, hm]
      · exfalso
        apply h
        use m
  · -- EXERCISE (*)
    rintro ⟨k, rfl⟩
    rw [mpow_mul, mpow_order, mpow_id]
  done

lemma mpow_nonzero_order (n : ℕ) (hn : n ≠ 0) (h : order x ≠ 0) : order (mpow x n) ≠ 0 := by
  have : ∃ m ≠ 0, mpow x m = 𝕖
  · exact order_nonzero x h
  obtain ⟨m, hm⟩ := this
  suffices : ∃ k ≠ 0, mpow (mpow x k) m = 𝕖
  · obtain ⟨k, hk⟩ := this
    suffices : order x ∣ k
    · sorry
    sorry
  use n
  apply And.intro
  · exact hn
  · rw [←mpow_mul, mul_comm, mpow_mul, hm.right, mpow_id]

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

-- lemma inv_unique_of_nonzero_order {y y' : M} (h : order x ≠ 0) (hy : μ x y = 𝕖) (hy' : μ x y' = 𝕖)
--   : y = y' := by
--   sorry

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
    rw [←mpow_mod_order]
    rw [←op_id (mpow x (k % order x))]
    have this : ∃ y : M, μ (mpow x m) y = 𝕖 := sorry
    obtain ⟨y, hy⟩ := this
    rw [←hy, ←op_assoc, ←mpow_add]
    have : k % order x = k := sorry
    rw [this, add_comm, hk, hy]
    sorry

  · rw [←hk] at hn
    linarith
  done

theorem mod_order_eq_of_mpow_eq (h : order x ≠ 0)
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

theorem gpow_order : gpow x (order x) = 𝕖 := by
  rw [gpow_ofNat, mpow_order]

theorem gpow_order_zero {n : ℤ} (h₀ : order x = 0) : gpow x n = 𝕖 → n = 0 := by
  intro h
  cases n with
  | ofNat n =>
    congr
    exact mpow_order_zero x n h₀ h
  | negSucc n =>
    -- TODO: this is not elegant
    have inv_inj : ∀ a b : G, ι a = ι b → a = b := sorry -- inverse injective
    rw [gpow_negSucc, mpow_succ_right, ←inv_id] at h
    sorry
    -- apply inv_inj at h
    -- apply mpow_order_zero at h
    -- linarith
    -- exact h₀

theorem gpow_mod_order {n : ℤ} : gpow x (n % order x) = gpow x n := by
  -- EXERCISE (**)
  cases n with
  | ofNat n =>
    have : (n : ℤ) % (↑(order x)) = (n % order x : ℕ) := rfl
    rw [Int.ofNat_eq_coe, this, gpow_ofNat, gpow_ofNat, mpow_mod_order]
  | negSucc n =>
    sorry

theorem gpow_inj_of_order_zero {m n : ℤ} (h : order x = 0) (heq : gpow x m = gpow x n) : m = n := by
  induction n using Int.induction_on generalizing m with
  | hz =>
    apply gpow_order_zero x h
    exact heq
  | hp n ih =>
    sorry
  | hn n ih =>
    sorry

-- theorem order_zero_of_gpow_inj (hinj : ∀ m n : ℤ, gpow x m = gpow x n → m = n)
--   : order x = 0 := by
--   sorry

theorem mod_order_eq_of_gpow_eq {m n : ℤ}
  : gpow x m = gpow x n → m % (order x) = n % (order x) := by
  sorry

end GroupOrder
