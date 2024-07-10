import AlgebraInLean.Chapter02.Sheet02

namespace AlgebraInLean

/-

## Isomorphisms

In Mathlib, isomorphisms come with additional structure; they are not simply defined as bijective
homomorphisms.

They are defined as a structure, bundled up with some useful fields:
- `to_fun` (a map from a group G → group H)
- `inv_fun` (a map from group H → group G)
- `left_inv` & `right_inv` (both inverses exist, thus a unique inverse exists)
- `map_mul'` (a proof of homomorphism/preservation of operation)

So to prove an isomorphism, we have to provide proofs for each of these fields.

Mathlib also lets us say that two groups are isomorphic by using the symbol `≃+` for additive
groups, and `≃*` for multiplicative groups.

Using this structure, we can come up with an arbitrary bijection and prove that it is an isomorphism
(or not), like in the trivial example below. The identity map that takes each element of the
additive group of integers to itself is clearly an isomorphism. In fact, as you might've guessed,
this holds for any arbitrary group.

-/

/- The identity map is an isomorphism -/
example (φ : ℤ → ℤ) (h1 : ∀ x, φ x = x) : ℤ ≃+ ℤ := by
  let hom_map : ℤ ≃ ℤ := by
    constructor
    have ha : Function.LeftInverse φ φ
    -- Function.LeftInverse g f means that g is a left inverse to f. Ditto for
    -- RightInverse, aside from the obvious difference.
    · intro x
      repeat rw [h1]
    exact ha
    have hb : Function.RightInverse φ φ
    · intro x
      repeat rw [h1]
    exact hb
  constructor
  intro x y
  have hc : hom_map.toFun = φ := by rfl
  rw [hc, h1 x, h1 y]
  exact h1 (x + y)

/-

What about the bijection that takes each member of the additive group of integers to its negation?
Is this an isomorphism? This proof will be extremely similar to the example above.

Since we are using integers in this proof, you might find the tactic `linarith` helpful.

-/

example (φ : ℤ → ℤ) (h1 : ∀ x, φ x = -x) : ℤ ≃+ ℤ := by
  -- SAMPLE SOLUTION
  let hom_map : ℤ ≃ ℤ := by
    constructor
    have ha : Function.LeftInverse φ φ
    · intro x
      simp [h1]
    exact ha
    have hb : Function.RightInverse φ φ
    · intro x
      simp [h1]
    exact hb
  constructor
  intro x y
  have hc : hom_map.toFun = φ := by rfl
  rw [hc]
  simp [h1]
  linarith
-- END SAMPLE SOLUTION

/-

Consider the bijection ℤ → ℤ that maps x to x + 1. Is this an isomorphism? Where does the proof
break?

-/
example (φ : ℤ → ℤ) (h1 : ∀ x, φ x = x + 1) : ℤ ≃+ ℤ := by
  -- SAMPLE SOLUTION
  let hom_map : ℤ ≃ ℤ := by
    constructor
    have ha : Function.LeftInverse (fun x => x - 1) φ
    · intro x
      rw [h1 x]
      exact Int.add_sub_cancel x 1
    exact ha
    have hb : Function.RightInverse (fun x => x - 1) φ
    · intro x
      rw [h1 (x - 1)]
      linarith
    exact hb
  constructor
  intro x y
  have hc : hom_map.toFun = φ := by rfl
  rw [hc]
  sorry
  -- END SAMPLE SOLUTION

/-

Optional: Uncomment the code template below, try choosing a group and a bijection, and prove that
the map is an isomorphism (or conversely, prove that it is not an isomorphism). Fill in the
underscores with your preferred groups, bijection, and proofs. An example might be a map from the
group of integers to itself, the map being the function that takes an integer x to 2x.

-/

/-

example (φ : _ → _) (h1 : ∀ _) : _ ≃_ _ := by
  let hom_map : _ ≃ _ := by
  { constructor
    have ha : Function.LeftInverse φ φ
    · sorry
    sorry
    have hb : Function.RightInverse φ φ
    · sorry
    sorry
  }
  sorry

-/

/-

Group isomorphisms from a group to itself, also called automorphisms, might seem uninteresting at
first. Any group will have at least one induced automorphism: the identity map. Boring. However,
there are much more interesting examples of nontrivial automorphisms, which you will focus on next
chapter; we'll also be pivoting back to our implementation of morphisms.

-/
