import AlgebraInLean.Basic
import AlgebraInLean.Chapter2.Sheet1
import Mathlib.Tactic

namespace Sheet2

namespace Defs

-- ## Homomorphisms and Isomorphisms

-- In Mathlib, isomorphisms come with additional structure; they are not simply defined as bijective homomorphisms.

-- They are defined as a structure, bundled up with some useful (and some essential) fields: 
-- - to_fun (a map from a group G → group H)
-- - inv_fun (a map from group H → group G)
-- - left_inv & right_inv (both inverses exist and they are unique)
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
  let hom : ℤ ≃ ℤ := by
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
  have hc : hom.toFun = φ := by rfl
  rw [hc]
  simp [h1]

-- What about the bijection that takes each member of the additive group of
-- integers to its negative? Is this an isomorphism? This proof will be
-- extremely similar to the example above.

-- Since we are using integers in this proof, you might find the tactic
-- `linarith` helpful.

-- Exercise
example (φ : ℤ → ℤ) (h1 : ∀ x, φ x = -x) : ℤ ≃+ ℤ := by
  let hom : ℤ ≃ ℤ := by
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
  have hc : hom.toFun = φ := by rfl
  rw [hc]
  simp [h1]
  linarith

-- Optional: Try choosing a group and a bijection, and prove that the map is an
-- isomorphism (or conversely, prove that it is not an isomorphism). Fill in
-- the underscores with your preferred groups, bijection, and proofs. An
-- example might be a map from the group of integers to itself, the map being
-- the function that takes an integer x to 2x.

example (φ : _ → _) (h1 : ∀ _) : _ ≃_ _ := by
  let hom : _ ≃ _ := by
  { constructor
    have ha : Function.LeftInverse φ φ
    · sorry
    sorry
    have hb : Function.RightInverse φ φ
    · sorry
    sorry
  }
  sorry

-- Let's prove that for every isomorphism φ which maps from a group G to
-- another group G', that there exists another isomorphism φ' which maps from
-- G' to G.

def iso_symm (φ : G → G') (hi : Isomorphism φ) : (φ' : G' → G) := by
  sorry

-- Let's prove that any group G is isomorphic to itself.

def iso_refl (φ : G → G') (hi : Isomorphism φ) : (φ' : G' → G) := by
  sorry

-- Let's prove that if a group G is isomorphic to group H, and group H is isomorphic to a group I, then the group G must be isomorphic to group I.

def iso_trans (φ : G → G') (hi : Isomorphism φ) : (φ' : G' → G) := by
  sorry

-- We have just proved that group isomorphisms form an equivalence relation
-- over all groups in general!

-- We have seen equivalence relations before: equality is an equivalence
-- relation. Formally, they are defined as a binary relation `∼` (often
-- pronounced "sim" and written `\sim`) over a set S such that:

-- - Reflexive; ∀ a ∈ S, a ∼ a
-- - Symmetric; ∀ a, b ∈ S, a ∼ b → b ∼ a
-- - Transitive; ∀ a, b, c ∈ S, a ∼ b and b ∼ c → a ∼ c

-- Group isomorphisms from a group to itself might seem uninteresting at first;
-- the more simple example being the identity mapping, which we showed was an
-- isomorphism at the beginning of this sheet. However, there are interesting
-- examples of nontrivial group-to-itself isomorphisms, which you will focus on next chapter.
