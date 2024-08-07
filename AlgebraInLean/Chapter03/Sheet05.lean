import AlgebraInLean.Chapter03.Sheet04

namespace AlgebraInLean

set_option linter.unusedTactic false

variable {G G' : Type*} [Group G] [Group G']

/--
This naturally leads to the idea of the kernel of a homomorphism. Generally, when a group G acts on
a set S, the kernel of the action is defined as {g ∈ G | g ⬝ s = s ∀ s ∈ S}. For a homomorphism φ :
G → G', the kernel of φ (kerφ) is defined by {g ∈ G | φ (g) = 𝕖}. Try proving that the kernel of a
homomorphism is a subgroup of G.
-/
def Kernel (φ : G → G') (h : Homomorphism φ) : Subgroup G where
  carrier := {g | φ g = 𝕖}
  -- EXERCISES
  has_id := by
    suffices : φ 𝕖 = 𝕖
    · exact this
    exact hom_id_to_id φ h
  mul_closure := by
    intro a b ha hb
    rw [Set.mem_setOf_eq, ←h, ha, hb, id_op]
  inv_closure := by
    intro a ha
    rw [Set.mem_setOf_eq, hom_inv_to_inv φ, ha, inv_id]
    exact h

/--
The image of a homomorphism φ is a subgroup of G' (not G as the kernel was) that contains all
elements which φ maps to. That is, all elements g' ∈ G' such that there is some element g ∈ G where
φ(g) = g'.

Try proving that the image of a homomorphism is a subgroup of G'.
-/
def Image (φ : G → G') (h : Homomorphism φ) : Subgroup G' where
  carrier := {x : G' | ∃ g, φ g = x}
  -- EXERCISES
  has_id := by
    use 𝕖
    rw [hom_id_to_id φ]
    exact h
  mul_closure := by
    intro a b ⟨x, hx⟩ ⟨y, hy⟩
    use μ x y
    rw [←h, hx, hy]
  inv_closure := by
    intro a ⟨x, hx⟩
    use ι x
    rw [←hx, hom_inv_to_inv φ]
    exact h

/-
Let's give `simp` access to some simple theorems.

Firstly, conjugating an element g by 𝕖 gives g back. Can you see why this works?
-/
@[simp]
theorem conjugate_by_id : conjugate (𝕖 : G) = id := by
  -- EXERCISE
  funext g
  rw [conjugate, id_op, inv_id, op_id]
  rfl

/-- Secondly, conjugating 𝕖 by any element yields the identity. This uses the `op_inv` property. -/
@[simp]
theorem conjugate_id (g : G) : conjugate g 𝕖 = 𝕖 := by
  -- EXERCISE
  rw [conjugate, op_id, op_inv]

/--
Thirdly, the conjugate of `a · b` is just conjugate of `a` composed with conjugate of `b`.

Can you figure out how g · (a · b) · g⁻¹ = (g · a · g⁻¹) · (g · b · g⁻¹)?
-/
@[simp]
theorem conjugate_op (a b : G) : conjugate (μ a b) = conjugate a ∘ conjugate b := by
  funext s
  rw [conjugate, Function.comp_apply, inv_anticomm]
  repeat rw [conjugate]
  repeat rw [op_assoc]

/--
We'll use capital `Conjugate` to define conjugating a set by an element g. This notation is
equivalent to the set {g · s · g⁻¹ | s ∈ S}, that is {conjugate s | s : S}.
-/
@[simp]
def Conjugate (g : G) (S : Set G) : Set G := conjugate g '' S

/--
We define a subgroup to be `normal` if the subgroup is closed under conjugation with any element of
G.
-/
def normal (H : Subgroup G) : Prop :=
  ∀ g h : G, h ∈ H → conjugate g h ∈ H

theorem Minimal_normal : normal (Minimal G) := by
  -- EXERCISE
  intro g h hh
  rw [hh, conjugate_id]
  trivial

theorem Maximal_normal : normal (Maximal G) := by
  -- EXERCISE
  intro _ _ _
  trivial

-- Prove that for a homomorphism φ : G → G', the kernel of φ is a normal subgroup.
theorem Kernel_normal (φ : G → G') (h : Homomorphism φ) : normal (Kernel φ h) := by
  -- EXERCISE
  intro g k hk
  suffices : φ (conjugate g k) = 𝕖
  · exact this
  rw [conjugate, ←h, ←h, hk, op_id, h, op_inv, hom_id_to_id φ h]

/--
The normalizer of a set S (of a group G) is the set of all elements in G that when conjugated with S
return S. The normalizer will never be empty since 𝕖 conjugates in such a way. Now show that this
subset of G is a subgroup of G.
-/
def Normalizer (S : Set G) : Subgroup G where
  carrier := {g | ∀ s ∈ S, Conjugate g S = S}
  -- EXERCISES? These are hard...
  has_id := by
    intro s _
    rw [Conjugate, conjugate_by_id]
    simp
  mul_closure := by
    intro a b ha hb s hs
    specialize ha s hs
    specialize hb s hs
    rw [Conjugate] at *
    rw [conjugate_op, Set.image_comp, hb, ha]
  inv_closure := by
    intro a ha s hs
    nth_rw 1 [←ha s hs]
    rw [Conjugate]
    funext x
    rw [Conjugate, ←Set.image_comp, ←conjugate_op, inv_op, conjugate_by_id, Set.image_id]

/--
The centralizer of a set S (of a group G) is the set of all elements in G that commute with all
elements of S. This can be thought of a measure of how close a group is to being abelian.
-/
def Centralizer (S : Set G) : Subgroup G where
  carrier := {g | ∀ s ∈ S, μ g s = μ s g}
  has_id := by
    intro s _
    rw [id_op, op_id]
  mul_closure := by
    intro a b ha hb s hs
    rw [op_assoc, hb, ←op_assoc, ha, op_assoc] <;> exact hs
  inv_closure := by
    intro a ha s hs
    symm
    rw [←op_id s, ←op_inv a]
    repeat rw [←op_assoc]
    apply congr <;> try rfl
    rw [op_assoc, op_inv, op_id]
    nth_rw 1 [←id_op s]
    rw [←inv_op a]
    repeat rw [op_assoc]
    apply congr <;> try rfl
    apply congr <;> try rfl
    exact ha s hs

theorem Centralizer_def {S : Set G} {a : G} : a ∈ Centralizer S ↔ ∀ s ∈ S, μ a s = μ s a :=
  Iff.of_eq rfl

def Center : Subgroup G := Centralizer Set.univ

/--
We have the `AbelianGroup` type class that we defined in chapter 1, but here we codify a subgroup
being abelian into a `Prop`. This lends itself to nice proofs like the one below.
-/
def Abelian (H : Subgroup G) : Prop := ∀ (x y : G), x ∈ H → y ∈ H → μ x y = μ y x

theorem subgroup_abelian_iff_centralizer_self (H : Subgroup G)
  : H ≤ Centralizer H ↔ Abelian H := by
  constructor
  · intro h x y hx hy
    specialize h hx
    exact h y hy
  · intro h x hx s hs
    exact h x s hx hs

/-
A homomorphism is injective if and only if the kernel is trivial. The backwards proof is quite
simple, in order for a homomorphism φ : G → G' to be injective it must be that φ maps ONLY 𝕖 ∈ G to
𝕖 ∈ G'. The forward way is slightly more tricky, requiring you to show that if φ a = φ b then a =
b.

hint : try using Iff.intro to start the proof.
-/
theorem homomorphism_inj_iff_kernel_trivial (φ : G → G') (h : Homomorphism φ) :
    Function.Injective φ ↔ Kernel φ h = Minimal G := by
  -- EXERCISE
  apply Iff.intro
  · intro hinj
    apply le_antisymm
    · intro x hx
      change x = 𝕖
      apply hinj
      rw [hom_id_to_id φ h]
      exact hx
    · apply Minimal_smallest
  · intro hk x y hfeq
    have h1 : φ (μ x (ι y)) = μ (φ x) (φ (ι y)) := by
      rw [h]
    have h2 : (φ (ι y)) = ι (φ y):= by
      apply hom_inv_to_inv
      exact h
    rw [hfeq, h2, op_inv] at h1
    have h3 : μ x (ι y) ∈ Kernel φ h := by
      trivial
    rw [hk] at h3
    have h4 : μ x (ι y) = 𝕖 := by
      trivial
    have h5 : μ x (ι y) = 𝕖 → μ (μ x (ι y)) y = μ 𝕖 y := by
      intro ht
      rw [ht]
    apply h5 at h4
    rw [id_op, op_assoc, inv_op, op_id] at h4
    exact h4

/-
In order for a homomorphism φ : G → G' to be surjective, it must be that each element in G' is
mapped to by an element from G. That is, each element in G' is mapped to, so it must be that the
image is complete. Try proving both directions of the IFF proof here.
-/
theorem homomorphism_surj_iff_image_complete (φ : G → G') (h : Homomorphism φ) :
    Function.Surjective φ ↔ Image φ h = Maximal G' := by
  -- EXERCISE
  apply Iff.intro
  · intro hsurj
    apply le_antisymm
    · apply Maximal_largest
    · intro x _
      exact hsurj x
  · intro hcomp
    intro x
    suffices : x ∈ Image φ h
    · exact this
    rw [hcomp]
    trivial

theorem subgroup_normalizer_self (H : Subgroup G) : H ≤ Normalizer H := by
  intro g hg s _
  ext x
  constructor
  · intro h
    rw [Conjugate] at h
    obtain ⟨y , h₁, h₂⟩ :=  h
    rw [← h₂]
    rw [conjugate]
    apply Subgroup.mul_closure
    · apply Subgroup.mul_closure
      · exact hg
      · exact h₁
    · apply Subgroup.inv_closure
      exact hg
  · intro h
    rw [Conjugate]
    use μ (μ (ι g) (x)) g
    constructor
    · apply Subgroup.mul_closure
      · apply Subgroup.mul_closure
        · apply Subgroup.inv_closure
          exact hg
        exact h
      exact hg
    · simp only [conjugate, op_assoc, op_inv, op_id]
      rw [←op_assoc]
      simp only [op_inv, id_op]
