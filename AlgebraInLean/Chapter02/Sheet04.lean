import AlgebraInLean.Chapter02.Sheet03

set_option linter.unusedTactic false

namespace AlgebraInLean

variable {G : Type*} [Group G]

/- ## Endomorphisms and Automorphisms -/

/-

In Sheet 1 of this chapter, you were introduced to homomorphisms and isomorphisms. In this
sheet, we will take a deeper dive with morphisms and some attributes that definitionally
separate different kids of morphisms.

Particularly, we will begin with endomorphims.

We define an endomorphism to be a homorphism from an object onto itself. In the case of
`AlgebraInLean`, this means that a _group_ endomporphism is a group homomorphism from an
arbitrary group G back to itself.

As you have seen previously, in the context of Algebra, "group" is often omitted when discussing
group endomorphisms. An endomorphism (and morphisms in general) can be defined among many
different types of mathematical objects, but in AlgebraInLean it will always refer to a group
endomorphism.

Let's take a look at how this would be defined in Lean:
-/
def Endomorphism (φ : G → G) : Prop := Homomorphism φ

/-

A fairly simple definition, but important as we move on.

Aside from group endomorphisms, a common example of an endomorphism is in linear algebra when
considering some vector space V. f: V → V is an endomorphism on a vector space V, and we define
_End(V)_ to be the set of all endomorphisms of V, which we know to be nonempty because of the
existence of the endomorphism mapping some arbitrary vector v ↦ 0, and the identity mapping
v ↦ v.

-/



/- An automorphism is defined to be an endomorphism that is also a bijection. You will recognize
the following definition is similar to how we defined bijectivity in the first place. -/
def Automorphism (φ : G → G) : Prop := Endomorphism φ ∧ Bijective φ
/-

You can think of it like a permutation from a group to itself, although it is important that
this permutation respects the group structure. see more specifically what "respecting the group
structure" looks like in the next chapter (keep an eye out for orders!).

-/

/- You may be able to intuitively discern that all automorphisms are also isomoprhisms.
Lets do a brief exercise to prove this before jumping into some more complex examples. -/
theorem aut_isomoprhism (φ : G → G) (h : Automorphism φ) : Isomorphism φ := by
  -- SAMPLE SOLUTION
  obtain ⟨h_endomorphism, h_bijective⟩ := h
  unfold Isomorphism
  constructor
  · unfold Endomorphism at h_endomorphism
    exact h_endomorphism
  · exact h_bijective
  -- END SAMPLE SOLUTION
  done


/-

As another exercise, let's prove that a specific function mapping within the group of integers
under addition is a group automorphism.

Specifically, fix G = ⟨ℤ, +⟩, and φ : G → G, x ↦ -x (the function fx = -x).

Note that in order to prove this, we do not necessarily need to "prove" that our φ is an
endomorphism. We are already defining it as the map φ : G → G (a group onto itself), so it
suffices to prove that φ is a homomorphism. That may be useful going forward with this proof.

-/

/- A brief definition of our φ: -/
def φ (x : ℤ) : ℤ := -x
/- φ : G → G, x ↦ -x -/

/- Show that φ is a group automorphism -/
theorem φ_automorphism : ∀ x y : ℤ, φ (x + y) = φ x + φ y ∧ Bijective φ := by
  -- SAMPLE SOLUTION
  intros x y
  constructor
  /- Prove homomorphism -/
  · unfold φ
    rw [neg_add]
  /- Prove Bijectivity -/
  · rw [Bijective]
    constructor
    /- Injectivity -/
    · intros x y h
      unfold φ at h
      exact neg_inj.mp h
    /- Surjectivity -/
    · intro z
      use -z
      unfold φ
      rw [neg_neg]
  -- END SAMPLE SOLUTION
  done


/-

Now that you have done a basic proof with automorphisms, we will move on to one that is slightly
more complex (which also introduces a new concept). _conjugation_ is defined to be the specific
relation between two elements of some group where a,b ∈ G are _conjugates_ if there is also some
g ∈ G such that b = gag⁻¹

Specifically, in the case of the general linear group of invertible matrices, _GL(n)_, this
conjugacy relation is called matrix similarity, which may be more familiar. (Recall that two
matrices A,B are similar iff there is also some matrix D such that B = DAD⁻¹).

We claim that conjugation is an automorphism under an arbitrary group and group operation,
meaning:

ψ : G → G, x ↦ gxg⁻¹ is a group automorphism. Let's prove this!

As with before, a brief definition of our ψ:

-/
def Conjugate (g x : G) : G := μ (μ g x) (ι g)
/- We define this specifically to be `Conjugate`, however we will also refer to this mapping
as ψ. It is common to see φ and ψ to represent these homomorphic and automorphic maps, but since
conjugation will come back up later, this definition is named as such. -/


/-

This definition, because it is under an arbitrary group operation, has to conform with the
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
-/

/- Show that ψ is a group automorphism -/
theorem ψ_automorphism (g : G) : ∀ x y : G, Conjugate g (μ x y) = μ (Conjugate g x)
(Conjugate g y) ∧ Bijective (Conjugate g) := by
  -- SAMPLE SOLUTION
  intros x y
  constructor
  -- Prove homomorphism
  · unfold Conjugate
    simp only [op_assoc]
    rw[← op_assoc (ι g), inv_op, id_op]
  -- Prove bijectivity
  · rw[Bijective]
    constructor
    -- Injectivity
    · intros x y h
      unfold Conjugate at h
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
      unfold Conjugate
      simp only [op_assoc]
      rw [← op_assoc g, op_inv, id_op, op_id]
    -- END SAMPLE SOLUTION
  done

/-

That proof was tough! But, it was a great exercise for you to prove in the most arbitrary sense,
since such a proof will be useful later when learning about group actions and automorphism
groups (meaning this sheet will likely be referenced in later chapters as one to come back to)!

-/


/- That's all we have for morphisms. Feel free to move on to Chapter 3: Subgroups!
## HAVE FUN! -/
