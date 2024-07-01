-- import «AlgebraInLean».Chapter2.Sheet1
import «AlgebraInLean».Basic  -- ## [FIX ME] - IMPORT ISSUES?
import Mathlib.Tactic

namespace Defs

namespace Morphisms

namespace Sheet3

-- ## NEED TO BE REMOVED LATER, NEED TO RESOLVE IMPORT ISSUE
-- See comment at top of sheet, Line 1.

-- Injectivity, Surjectivity, Bijectivity
  def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y

  def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y

  def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)

  -- Basic Morphisms ("imported" from Sheet 1)
  def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ
  a) (φ b) = φ (μ a b)

  def Isomorphism [Group G] [Group H] (φ : G → H) : Prop := (Homomorphism φ ∧
  Bijective φ)

-- ## Automorphisms, etc.

  section Endomorphisms
    -- In Sheet 1 of this chapter, you were introduced to homomorphisms
    -- and isomoprhisms. In this sheet, we will take a deeper dive with
    -- morphisms and some attributes that definitionally separate
    -- different kids of morphisms.

    -- Particularly, we will begin with endomorphims.

    -- We define an endomorphism to be a homorphism from an object onto
    -- itself. In the case of `AlgebraInLean`, this means that a _group_
    -- endomporphism is a group homomorphism from an abritrary group G
    -- back to itself.
    -- As you have seen previously, in the context of Algebra, "group"
    -- is often omitted when discussing group endomorphisms.
    -- An endomorphism (and morphisms in general) can be defined
    -- among many different types of mathematical objects, but in AlgebraInLean it
    -- will always refer to a group endomorphism.

    -- Let's take a look at how this would be defined in Lean:
    def Endomorphism [Group G] (φ : G → G) : Prop := Homomorphism φ
    -- A fairly simple definition, but important as we move on.

    -- Aside from group endomorphisms, a common example of an endomorphism is
    -- in linear algebra when considering some vector space V.
    -- f: V → V is an endomorphism on a vector space V, and we define _End(V)_
    -- to be the set of all endomorphisms of V, which we know to be nonempty
    -- because of the existence of the endomorphism mapping some arbitrary vector
    -- v ↦ 0, and the identity mapping v ↦ v.

  end Endomorphisms

  section Automorphisms
    -- An automorphism is defined to be an endomorphism that is also a bijection.
    -- You will recognize the following definition is similar to how we defined
    -- bijectivity in the first place.

    def Automorphism [Group G] (φ : G → G) : Prop := Endomorphism φ ∧ Bijective φ

    -- You can think of it like a permutation from a group to itself, although it
    -- is important that this permutation respects the group structure.
    -- see more specifically what "respecting the group structure" looks like in
    -- the next chapter (keep an eye out for orders!).

    -- ## EXAMPLES HERE ?

    -- As an exercise, let's prove that a specific function mapping within the
    -- group of integers under addition is a group automorphism.

    -- Spefically, fix G = ⟨ℤ, +⟩, and φ : G → G, x ↦ -x
    -- (the function fx = -x).

    -- Note that in order to prove this, we do not necessarily need to "prove" that
    -- our φ is an endomorphism. We are already defining it as the map φ : G → G
    -- (a group onto itself), so it suffices to prove that φ is a homomorphism.
    -- That may be useful going forward with this proof.

    -- A brief definition of our φ:
    def φ (x : ℤ) : ℤ := -x
    -- φ : G → G, x ↦ -x

    -- Show that φ is a group automorphism
    theorem φ_group_automorphism : ∀ x y : ℤ, φ (x + y) = φ x + φ y ∧ Bijective φ := by
      intros x y
      apply And.intro
      -- Prove homomorphism
      unfold φ
      rw[neg_add]
      -- Prove Bijectivity
      rw[Bijective]
      apply And.intro
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



  end Automorphisms

-- ## OLD ↓ ↓

-- TODO: Do we provide toy examples of automorphisms? Or do we define
-- conjugation and then go straight into proving that conjugation is an
-- automorphism?

end Sheet3
