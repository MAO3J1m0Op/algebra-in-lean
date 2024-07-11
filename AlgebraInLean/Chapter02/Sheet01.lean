import AlgebraInLean.Chapter02.Sheet00

namespace AlgebraInLean

/-
Given a group G and a group H, a group homomorphism is a map φ from G to H which "preserves" or
"respects" the group structure. That is, given elements a, b ∈ G, φ(a ⬝ b) = φ(a) ⬝ φ(b).

In other words, you can combine a and b in G, and then apply φ, or apply φ to a and b individually,
and then combine them in H.

Group homomorphisms are a particular case of homomorphisms in algebra, which are maps between
algebraic structures (like monoids or semigroups) that preserve the algebraic structure like this.
These are a kind of an even more general concept of a "morphism" from category theory:
<https://en.wikipedia.org/wiki/Category_theory>.

Mathematicians often omit the structure of the morphism (or homomorphism) when it can be deduced
from context, so these will often be called just "homomorphism" rather than "group homomorphism".
-/

variable {G H K : Type*} [Group G] [Group H] [Group K]

def Group.Homomorphism (φ : G → H) : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

/-
Part of what we mean when we say a homomorphism "respects the group structure" is that homomorphisms
(and therefore isomorphisms) map inverses elements of group G to corresponding inverse elements of
group H. We will explore this and examples like these in the following exercise.

Below are some basic proofs of homomorphisms: that they map identities to identities, and inverses
to inverses.
-/

/-- For a homomorphism φ, φ(e) = e -/
theorem Group.homomorphism_id {φ : G → H} (h : Homomorphism φ) : φ 𝕖 = 𝕖 := by
  -- SAMPLE SOLUTION
  specialize h 𝕖 𝕖
  apply left_cancel (φ 𝕖)
  rw [op_id] at *
  exact h
  -- END SAMPLE SOLUTION

/-- For a homomorphism φ, φ(a⁻¹) = φ(a)⁻¹ -/
theorem Group.homomorphism_inv {φ : G → H} (h : Homomorphism φ) (g : G) : φ (ι g) = ι (φ g) := by
  -- SAMPLE SOLUTION
  apply inv_unique_left
  rw [h, inv_op, homomorphism_id h]
  -- END SAMPLE SOLUTION


/- Here are a few examples of group homomorphisms -/

/- Hint: `simp` is useful here -/
/-- The function that maps everything to the identity is a group homomorphism -/
theorem Group.const_id_homomorphism : Homomorphism (λ (_ : G) ↦ (𝕖 : H)) := by
  -- SAMPLE SOLUTION
  intro a b
  simp only []
  exact op_id 𝕖
  -- END SAMPLE SOLUTION
  done

/-
Note that `id` here refers to the identity function (the function that maps everything to itself)
rather than to the group identity element.
-/
/-- The identity function is a group homomorphism -/
theorem Group.id_homomorphism : Homomorphism (id : G → G) := by
  -- SAMPLE SOLUTION
  intro a b
  rfl
  -- END SAMPLE SOLUTION
  done


/-- The composition of homomorphisms is a homomorphism -/
theorem Group.homomorphism_comp {φ : G → H} {ψ : H → K} (hφ : Homomorphism φ) (hψ : Homomorphism ψ)
  : Homomorphism (ψ ∘ φ) := by
  -- SAMPLE SOLUTION
  intro a b
  simp
  rw [hψ, hφ]
  -- END SAMPLE SOLUTION
  done


/-
You have two options on where to go next. If you're familiar with basic modular arithmetic
(including GCDs, LCMs, and the Euclidean algorithm), you can go straight to sheet 3. If you wish to
learn how these are implemented in Lean or simply want a refresher, you should continue to sheet 2
instead.
-/
