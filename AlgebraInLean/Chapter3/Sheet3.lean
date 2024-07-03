import «AlgebraInLean».Chapter3.Sheet2

namespace Defs
  namespace Subgroups

    variable {G G' : Type*} [Group G] [Group G']

    -- Based on what we know about homomorphisms and group identities, it should be that a
    -- homomorphism maps the identity of the domain to the identity of the codomain.
    -- Let's prove it.
    theorem homomorphism_id_map_id (φ : G → G') (hφ : Homomorphism φ) : φ (𝕖 : G) = (𝕖 : G') := by
      -- EXERCISE
      have h1 : φ 𝕖 = μ (φ 𝕖) (φ 𝕖) := by
        rw [hφ, op_id]
      have h2 : φ 𝕖 = μ (φ 𝕖) (φ 𝕖) → μ (φ 𝕖) (ι (φ 𝕖)) = μ (μ (φ 𝕖) (φ 𝕖) ) (ι (φ 𝕖)) := by
        intro he
        rw [← he]
      apply h2 at h1
      rw[op_assoc, op_inv, op_id] at h1
      symm
      exact h1

    -- One property that follows directly from the last is that for any a ∈ G, φ(a⁻¹) = φ(a)⁻¹.
    -- We can show this by using φ(𝕖) = φ(a · a⁻¹) = φ(a) · φ(a⁻¹) and the uniqe identity property.
    theorem homomorphism_id_inv (φ : G → G') (hφ : Homomorphism φ) : ∀ a : G, φ (ι a) = ι (φ a) := by
      -- EXERCISE
      intro a
      have h1 : φ 𝕖 = 𝕖 := by
        apply homomorphism_id_map_id
        exact hφ
      have h2 : φ (μ a (ι a)) = μ (φ a) (φ (ι a)) := by
        rw [hφ]
      rw [op_inv, h1] at h2
      sorry --complete proof with unique inverse theorem

    -- This naturally leads to the idea of the kernel of a homomorphism. Generally, when a group G
    -- acts on a set S, the kernel of the action is defined as {g ∈ G | g ⬝ s = s ∀ s ∈ S}.
    -- For a homomorphism φ : G → G', the kernel of φ (kerφ) is defined by {g ∈ G | φ (g) = 𝕖}.
    -- Try proving that the kernel of a homomorphism is a subgroup of G.
    def Kernel (φ : G → G') (h : Homomorphism φ) : Subgroup G where
      carrier := {g | φ g = 𝕖}
      -- EXERCISES
      nonempty := by
        suffices : φ 𝕖 = 𝕖
        · exact this
        exact homomorphism_id_map_id φ h
      mul_closure := by
        intro a b ha hb
        rw [Set.mem_setOf_eq, ←h, ha, hb, id_op]
      inv_closure := by
        intro a ha
        rw [Set.mem_setOf_eq, homomorphism_id_inv φ, ha, inv_id]
        exact h

    -- The image of a homomorphism φ is a subgroup of G' (not G as the kernel was) that contains all
    -- elements which φ maps to. That is, all elements g' ∈ G' such that there is some element g ∈ G
    -- where φ(g) = g'.
    -- Try proving that the image of a homomorphism is a subgroup of G'.
    def Image (φ : G → G') (h : Homomorphism φ) : Subgroup G' where
      carrier := {x : G' | ∃ g, φ g = x}
      -- EXERCISES
      nonempty := by
        use 𝕖
        rw [homomorphism_id_map_id φ]
        exact h
      mul_closure := by
        intro a b ⟨x, hx⟩ ⟨y, hy⟩
        use μ x y
        rw [←h, hx, hy]
      inv_closure := by
        intro a ⟨x, hx⟩
        use ι x
        rw [←hx, homomorphism_id_inv φ]
        exact h

    -- The conjugate of an element n by g is defined as the specific left and right operations
    -- g · n · g⁻¹.
    -- Note that g and n are in group G so the conjugate also exists in G.
    def conjugate (g n : G) : G := μ (μ g n) (ι g)

    -- Let's give simp access to some simple theorems.
    -- Firstly, conjugating an element g by 𝕖 gives g back. Can you see why this works?
    @[simp]
    theorem conjugate_by_id : conjugate (𝕖 : G) = id := by
      -- EXERCISE
      unfold conjugate
      funext g
      rw [id_op, inv_id, op_id]
      rfl

    -- Secondly, conjugating 𝕖 by any element yields the identity. This uses the op_inv property.
    @[simp]
    theorem conjugate_id (g : G) : conjugate g 𝕖 = 𝕖 := by
      -- EXERCISE
      unfold conjugate
      rw [op_id, op_inv]

    -- Thirdly, the conjugate of `a · b` is just conjugate of `a` composed with conjugate of `b`.
    -- Can you figure out how g · (a · b) · g⁻¹ = (g · a · g⁻¹) · (g · b · g⁻¹)?
    @[simp]
    theorem conjugate_op (a b : G) : conjugate (μ a b) = conjugate a ∘ conjugate b := by
      funext s
      unfold conjugate
      rw [Function.comp_apply, inv_anticomm]
      simp only [op_assoc]

    -- We'll use capital `Conjugate` to define conjugating a set by an element g. This notation is
    -- equivalent to the set {g · s · g⁻¹ | s ∈ S}, that is {conjugate s | s : S}.
    def Conjugate (g : G) (S : Set G) : Set G := conjugate g '' S

    -- We define a subgroup to be `normal` if the subgroup is closed under
    -- conjugation with any element of G.
    def normal (H : Subgroup G) : Prop :=
      ∀ g h : G, h ∈ H → conjugate g h ∈ H

    -- Try proving that the Minimal subgroup defined in sheet 1 is a normal subgroup.
    theorem Minimal_normal : normal (Minimal G) := by
      -- EXERCISE
      intro g h hh
      rw [hh, conjugate_id]
      trivial

    -- Try proving that the Maximal subgroup define din sheet 1 is a normal subgroup.
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
      unfold conjugate
      rw [←h, ←h, hk, op_id, h, op_inv, homomorphism_id_map_id φ h]

    -- The normalizer of a set S (of a group G) is the set of all elements in G that when conjugated
    -- with S return S. The normalizer will never be empty since 𝕖 conjugates in such a way. Now
    -- show that this subset of G is a subgroup of G.
    def Normalizer (S : Set G) : Subgroup G where
      carrier := {g | ∀ s ∈ S, Conjugate g S = S}
      -- EXERCISES? These are hard...
      nonempty := by
        intro s _
        unfold Conjugate
        rw [conjugate_by_id]
        simp
      mul_closure := by
        intro a b ha hb s hs
        specialize ha s hs
        specialize hb s hs
        unfold Conjugate at *
        rw [conjugate_op, Set.image_comp, hb, ha]
      inv_closure := by
        intro a ha s hs
        nth_rw 1 [←ha s hs]
        unfold Conjugate
        funext x
        dsimp only
        rw [←Set.image_comp, ←conjugate_op, inv_op, conjugate_by_id, Set.image_id]

    -- The centralizer of a set S (of a group G) is the set of all elements in G that commute with
    -- all elements of S. The centralizer will never be empty since 𝕖 commutes in such a way. Now
    -- show that this subset of G is a subgroup of G. What would happen if G is abelian?
    def Centralizer (S : Set G) : Subgroup G where
      -- FIXME : all are written with primitive group axioms. If more robust
      -- ones are provided in ch. 1, we can work to use those instead.
      carrier := {g | ∀ s ∈ S, μ g s = μ s g}
      nonempty := by
        intro s hs
        rw [id_op, op_id]
      mul_closure := by
        intro a b ha hb s hs
        rw [op_assoc, hb, ←op_assoc, ha, op_assoc] <;> exact hs
      inv_closure := by
        -- Nasty, but works
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

    -- The center of G is the subgroup of G with elements that commute with every element in G.
    def Center : Subgroup G := Centralizer Set.univ

    -- This may sound trivial, but try proving a subgroup H is normal if and only if its normalizer
    -- is the full subgroup H.
    theorem normal_normalizer (H : Subgroup G) : normal H ↔ Normalizer H = H := by
      -- EXERCISE
      -- TODO
      apply Iff.intro
      · intro hH
        apply le_antisymm
        · sorry
        · sorry
      · sorry

    -- A homomorphism is injective if and only if the kernel is trivial. The backwards proof is
    -- quite simple, in order for a homomorphism φ : G → G' to be injective it must be that φ maps
    -- ONLY 𝕖 ∈ G to 𝕖 ∈ G'. The forward way is slightly more tricky, requiring you to show that
    -- if φ a = φ b then a = b.
    -- hint : try using Iff.intro to start the proof.
    theorem homomorphism_inj_iff_kernel_trivial (φ : G → G') (h : Homomorphism φ) :
        Function.Injective φ ↔ Kernel φ h = Minimal G := by
      -- EXERCISE
      apply Iff.intro
      · intro hinj
        apply le_antisymm
        · intro x hx
          suffices : x = 𝕖
          · exact this
          apply hinj
          rw [homomorphism_id_map_id φ h]
          exact hx
        · apply Minimal_smallest
      · intro hk x y hfeq
        have h1 : φ (μ x (ι y)) = μ (φ x) (φ (ι y)) := by
          rw [h]
        have h2 : (φ (ι y)) = ι (φ y):= by
          apply homomorphism_id_inv
          exact h
        rw [hfeq, h2, op_inv] at h1
        have h3 : μ x (ι y) ∈ Kernel φ h := by
          trivial
        rw [hk] at h3
        have h4 : μ x (ι y) = 𝕖 := by
          trivial
        have h5 : μ x (ι y) = 𝕖 → μ (μ x (ι y)) y = μ 𝕖 y := by
          intro ht
          rw[ht]
        apply h5 at h4
        simp at h4
        exact h4

    -- In order for a homomorphism φ : G → G' to be surjective, it must be that each element in G'
    -- is mapped to by an element from G. That is, each element in G' is mapped to, so it must be
    -- that the image is complete. Try proving both directions of the IFF proof here.
    theorem homomorphism_surj_iff_image_complete  (φ : G → G') (h : Homomorphism φ) :
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

  end Subgroups
end Defs
