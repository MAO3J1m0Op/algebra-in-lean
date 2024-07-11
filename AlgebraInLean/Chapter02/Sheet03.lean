import AlgebraInLean.Chapter02.Sheet02

set_option linter.unusedTactic false

namespace AlgebraInLean

/-
An isomorphism is a special kind of homomorphism (or, more generally, morphism) with the additional
condition that it must be invertible. For a function φ, invertibility is the same as being
bijective, so we use that instead.

When there exists an isomorphism between two groups, they are said to be "isomorphic" (greek for
"equal shape"). Groups (or other algebraic structures) that are isomorphic are indistinguishable
from each other by structure alone, and this is often expressed by the phrase "equal up to
isomorphism".
-/

variable {G H K : Type*} [Group G] [Group H] [Group K]

def Group.Isomorphism (φ : G → H) : Prop := Homomorphism φ ∧ Bijective φ

def Group.Isomorphic (G H : Type*) [Group G] [Group H] : Prop := ∃ (φ : G → H), Isomorphism φ

/-
If we say that isomorphic groups are "indistinguishable", then we should certainly hope that a group
is isomorphic to itself. That is indeed the case, and the isomorphism is the identity function
-/
/-- The identity function is a group isomorphism -/
theorem Group.id_isomorphism : Isomorphism (id : G → G) := by
  -- SAMPLE SOLUTION
  constructor
  · exact id_homomorphism
  · constructor
    · intro x y h
      exact h
    · intro y
      use y
      rfl
  -- END SAMPLE SOLUTION
  done

/-- A group is isomorphic to itself -/
theorem Group.isomorphic_reflexive : Isomorphic G G := by
  -- SAMPLE SOLUTION
  use id
  exact id_isomorphism
  -- END SAMPLE SOLUTION
  done

/- The tactic `rintro`, which combines `intro` and `rcases` may be useful here -/
/-- If G is isomorphic to H and H is isomorphic to K, then G is isomorphic to K -/
theorem Group.isomorphic_transitive : Isomorphic G H → Isomorphic H K → Isomorphic G K := by
  -- SAMPLE SOLUTION
  rintro ⟨φ, ⟨hφ₁, hφ₂⟩⟩ ⟨ψ, ⟨hψ₁, hψ₂⟩⟩
  use ψ ∘ φ
  constructor
  · exact homomorphism_comp hφ₁ hψ₁
  · exact bijective_comp hφ₂ hψ₂
  -- END SAMPLE SOLUTION
  done

/-- If G is isomorphic to H, then H is isomorphic to G -/
theorem Group.isomorphic_symm : Isomorphic G H → Isomorphic H G := by
  -- SAMPLE SOLUTION
  rintro ⟨φ, ⟨hφ₁, hφ₂⟩⟩
  obtain ⟨ψ, hψ⟩ := inv_from_bijective hφ₂
  use ψ
  constructor
  · intro a b
    apply hφ₂.left
    rw [←hφ₁]
    have : ∀ (x : H), φ (ψ x) = x := by
      intro x
      rw [← @Function.comp_apply _ _ _ φ, hψ.right]
      rfl
    repeat rw [this]
  · apply bijective_from_inv
    use φ
    apply And.symm
    exact hψ
  -- END SAMPLE SOLUTION
  done

/-
These three properties (reflexivity, transitivity, and symmetry) make "being isomorphic" into an
equivalence relation. This idea will be explored further in quotient groups, and it shows up all the
time in mathematics.
-/


-- TODO: remove below


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
