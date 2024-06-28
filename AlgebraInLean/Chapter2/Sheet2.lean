import AlgebraInLean.Basic
import AlgebraInLean.Chapter2.Sheet1
import Mathlib.Tactic

namespace Sheet2

namespace Defs

-- ## Isomorphisms

-- In Mathlib, isomorphisms come with additional structure; they are not simply
-- defined as bijective homomorphisms.

-- They are defined as a structure, bundled up with some useful (and some
-- essential) fields:
-- - to_fun (a map from a group G → group H)
-- - inv_fun (a map from group H → group G)
-- - left_inv & right_inv (both inverses exist, thus a unique inverse exists)
-- - map_mul' (a proof of homomorphism/preservation of operation)

-- So to prove an isomorphism, we have to provide proofs for each of these
-- fields.

-- Mathlib also lets us say that two groups are isomorphic by using the symbol
-- `≃+` for additive groups, and `≃*` for multiplicative groups.

-- Using this structure, we can come up with an arbitrary bijection and prove
-- that it is an isomorphism (or not), like in the trivial example below. The
-- identity map that takes each element of the additive group of integers to
-- itself is clearly an isomorphism. In fact, as you might've guessed, this
-- holds for any arbitrary group.

-- Example, not exercise
example (φ : ℤ → ℤ) (h1 : ∀ x, φ x = x) : ℤ ≃+ ℤ := by
  let hom_map : ℤ ≃ ℤ := by
  { constructor
    have ha : Function.LeftInverse φ φ
    -- Function.LeftInverse g f means that g is a left inverse to f. Ditto for
    -- RightInverse, aside from the obvious difference.
    · intro x
      simp [h1]
    exact ha
    have hb : Function.RightInverse φ φ
    · intro x
      simp [h1]
    exact hb
  }
  constructor
  intro x y
  have hc : hom_map.toFun = φ := by rfl
  rw [hc]
  simp [h1]

-- What about the bijection that takes each member of the additive group of
-- integers to its negative? Is this an isomorphism? This proof will be
-- extremely similar to the example above.

-- Since we are using integers in this proof, you might find the tactic
-- `linarith` helpful.

-- Exercise
example (φ : ℤ → ℤ) (h1 : ∀ x, φ x = -x) : ℤ ≃+ ℤ := by
  let hom_map : ℤ ≃ ℤ := by
  { constructor
    have ha : Function.LeftInverse φ φ
    · intro x
      simp [h1]
    exact ha
    have hb : Function.RightInverse φ φ
    · intro x
      simp [h1]
    exact hb
  }
  constructor
  intro x y
  have hc : hom_map.toFun = φ := by rfl
  rw [hc]
  simp [h1]
  linarith

-- Optional: Try choosing a group and a bijection, and prove that the map is an
-- isomorphism (or conversely, prove that it is not an isomorphism). Fill in
-- the underscores with your preferred groups, bijection, and proofs. An
-- example might be a map from the group of integers to itself, the map being
-- the function that takes an integer x to 2x.

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
-- Don't worry about the term `Subgroup`, this will be defined very soon!
-- However, we can see that `zpowers` clearly refers to taking multiplicative
-- integer powers of a group element g, which tracks with our definition above.

-- Group isomorphisms from a group to itself (like the first example we looked
-- at) might seem uninteresting at first. Any group will have at least one
-- isomorphism associated with it: the identity map. Boring. However, there are
-- much more interesting examples of nontrivial group-to-itself isomorphisms,
-- which you will focus on next chapter; we'll also be pivoting back to our
-- implementation of morphisms.

-- We introduce a closely related group; the integers _modulo_ some integer n.

variable (G : ZMod n) (generators : Finset (ZMod n))

-- TODO: do we explain type class instantiation and et cetera?? seems like a
-- lot for this sheet to take on tbh. though we can totally split things up

-- ## EXERCISES:

-- TODO: Show that a map φ : n → gⁿ is a homomorphism from ℤ/3ℤ to C₃.

-- TODO: Show that a map φ : n → gⁿ is an isomorphism from ℤ/3ℤ to C₃.

-- TODO: Generalise the above: ℤ/nℤ is isomorphic to Cₙ, with the map being the
-- same.

/- ---------- -/


end Sheet2
