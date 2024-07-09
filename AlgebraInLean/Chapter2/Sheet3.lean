import «AlgebraInLean».Basic
import Mathlib.Tactic

namespace Defs

namespace Morphisms

namespace Sheet3

-- Injectivity, Surjectivity, Bijectivity
  def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y

  def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y

  def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)

  -- Basic Morphisms ("imported" from Sheet 1)
  def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ
  a) (φ b) = φ (μ a b)

  def Isomorphism [Group G] [Group H] (φ : G → H) : Prop := (Homomorphism φ ∧
  Bijective φ)

-- ## Endomorphisms and Automorphisms

  section Endomorphisms
    /-

    In Sheet 1 of this chapter, you were introduced to homomorphisms and isomorphisms. In this
    sheet, we will take a deeper dive into morphisms and some properties that allow us to classify
    them.

    Let's begin with endomorphisms.

    We define an endomorphism to be a homorphism from an object onto itself. In the case of
    `AlgebraInLean`, this means that a _group_ endomporphism is a group homomorphism from an
    abritrary group G back to itself. As you have seen previously, in the context of Algebra,
    "group" is often omitted when discussing group endomorphisms. An endomorphism (and morphisms in
    general) can be defined among many different types of mathematical objects, but in AlgebraInLean
    it will always refer to a group endomorphism.

    Let's take a look at how this would be defined in Lean:

    -/
    def Endomorphism [Group G] (φ : G → G) : Prop := Homomorphism φ

    /-

    A fairly simple definition, but important as we move on.

    Aside from group endomorphisms, another example you might've seen is an endomorphism f: V → V on
    a vector space V. We also define _End(V)_ to be the set of all endomorphisms of V, which we know
    to be nonempty because of the existence of the endomorphism mapping some arbitrary vector v ↦ 0,
    and the identity mapping v ↦ v.

    -/

  end Endomorphisms

  section Automorphisms

    /-

    An automorphism is defined to be an endomorphism that is also a bijection.
    You will recognize the following definition is similar to how we defined
    bijectivity in the first place.

    -/
    def Automorphism [Group G] (φ : G → G) : Prop := Endomorphism φ ∧ Bijective φ

    /-

    You can think of an automorphism as a permutation of the elements of a group that preserves the
    group structure. To see what "respecting the group structure" means formally, take a look at the
    next chapter (keep an eye out for orders!).

    As an exercise, let's prove that a specific function mapping within the group of integers under
    addition is a group automorphism.

    Spefically, fix G = ⟨ℤ, +⟩, and φ : G → G, x ↦ -x (the function fx = -x).

    Note that in order to prove this, we do not necessarily need to "prove" that our φ is an
    endomorphism. We are already defining it as the map φ : G → G (a group onto itself), so it
    suffices to prove that φ is a homomorphism. That may be useful going forward with this proof.

    -/

    -- A brief definition of our φ:
    def φ (x : ℤ) : ℤ := -x
    -- φ : G → G, x ↦ -x

    -- Show that φ is a group automorphism
    theorem φ_automorphism : ∀ x y : ℤ, φ (x + y) = φ x + φ y ∧ Bijective φ := by
      intros x y
      constructor
      -- Prove homomorphism
      · unfold φ
        rw[neg_add]
      -- Prove Bijectivity
      · rw[Bijective]
        constructor
        -- Injectivity
        · intros x y h
          unfold φ at h
          exact neg_inj.mp h
        -- Surjectivity
        · intro z
          use -z
          unfold φ
          rw[neg_neg]
      done


    /-

    Now that you have done a basic proof with automorphisms, we will move on to one that is slightly
    more complex (which also introduces a new concept). _conjugation_ is defined to be the specific
    relation between two elements of some group where a,b ∈ G are _conjugates_ if there exists some
    g ∈ G such that b = gag⁻¹

    Specifically, in the case of the general linear group of invertible matrices, _GL(n)_, this
    conjugacy relation is called matrix similarity, which may be more familiar. (Recall that two
    matrices A,B are similar iff there is also some matrix D such that B = DAD⁻¹).

    We claim that conjugation is an automorphism for any group. That is, ψ : G → G, x ↦ gxg⁻¹ is a
    group automorphism. Let's prove this!

    As with before, a brief definition of our ψ:

    -/
    def ψ [Group G] (g x : G) : G := μ (μ g x) (ι g)

    /-
    This definition, because it is under an arbitraty group action, has to conform with the
    definitions that we previously defined for groups. Don't worry too much if you don't understand
    the specific syntax here, but just know that μ is an arbitrary group operation, and (ι g) is
    g⁻¹.

    THIS PROOF WILL BE TOUGH, especially when it comes to the syntax of our arbitrary group
    operation definitions! As a reminder, `μ g x` means g*x, where * is the implicit group
    operation. `μ (y) (μ g x)` means y*(g*x). The associativity is important here as Lean will
    automatically associate group elements that directly follow the `μ` operator. However, using
    theorems from the group definitions sheet, you can rearrange this associativity (since that is a
    key part of a group definition anwyays)! You may want to revisit Chapter 1 for those theorems.

    Tip: You will want to approach this proof similarly to how you proved that the inversion
    function for integers under addition was a group automorphism. Split the proof up into its
    different components (i.e., proving the homorphism property and then the bijectivity property
    separately).

    The following helper lemmas may be helpful to you when proving the bijectivity property of the
    conjugation automorphism.

    -/
    lemma left_cancel [Group G] (x y g : G) (h : μ g x = μ g y) : x = y := by
      have h1 : μ g x = μ g y → μ (ι g) (μ g x) = μ (ι g) (μ g y) := by
        intro h
        rw [h]
      apply h1 at h
      rw [← op_assoc, inv_op, ← op_assoc, inv_op, id_op, id_op] at h
      exact h

    lemma right_cancel [Group G] (x y g : G) (h : μ x g = μ y g) : x = y := by
      have h1 : μ x g = μ y g → μ (μ x g) (ι g) = μ (μ y g) (ι g) := by
        intro h
        rw [h]
      apply h1 at h
      rw [op_assoc, op_inv, op_assoc, op_inv, op_id, op_id] at h
      exact h
    -- ## END HELPERS

    -- Show that ψ is a group automorphism
    theorem ψ_automorphism [Group G] (g : G) : ∀ x y : G, ψ g (μ x y) = μ (ψ g x) (ψ g y)
    ∧ Bijective (ψ g) := by
      intros x y
      constructor
      -- Prove homomorphism
      · unfold ψ
        simp only [op_assoc]
        rw[← op_assoc (ι g), inv_op, id_op]
      -- Prove bijectivity
      · rw[Bijective]
        constructor
        -- Injectivity
        · intros x y h
          unfold ψ at h
          have h1 : μ (μ g x) (ι g) = μ (μ g y) (ι g) → μ g x = μ g y := by
            intro h
            apply right_cancel at h
            exact h
          apply h1 at h
          apply left_cancel at h
          exact h
        -- Surjectivity
        · intro z
          use μ (ι g) (μ z g)
          unfold ψ
          simp only [op_assoc]
          rw [← op_assoc g, op_inv, id_op, op_id]
      done

    /-

    That proof was tough! But, it was a great exercise for you to prove in the most
    arbitrary sense, since such a proof will be useful later when learning about
    group actions and automorphism groups (meaning this sheet will likely be
    referenced in later chapters as one to come back to)!

    -/
  end Automorphisms

/-

That's all we have for morphisms. Feel free to move on to Chapter 3: Subgroups!
## HAVE FUN!

-/

end Sheet3
