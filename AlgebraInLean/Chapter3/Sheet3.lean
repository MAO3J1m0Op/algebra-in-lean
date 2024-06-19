import «AlgebraInLean».Chapter3.Sheet2

namespace Defs
  namespace Subgroups

    variable {G G' : Type*} [Group G] [Group G']

    -- TODO: will be imported
    def Homomorphism (φ : G → G') : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

    -- TODO: import from Chapter 1
    section FromChapter1

      variable {G : Type*} [Group G]

      theorem op_cancel_left (a u v : G) : μ a u = μ a v → u = v := sorry

      theorem op_cancel_right (a u v : G) : μ a u = μ a v → u = v := sorry

    end FromChapter1

    -- TODO: import from Chapter 2
    section FromChapter2

      variable (φ : G → G') (hφ : Homomorphism φ)

      theorem homomorphism_id_map_id : φ 𝕖 = 𝕖 := sorry

      theorem homomorphism_id_inv : ∀ a : G, φ (ι a) = ι (φ a) := sorry

    end FromChapter2

    def Kernel (φ : G → G') (h : Homomorphism φ) : Subgroup G where
      carrier := {g | φ g = 𝕖}
      -- EXERCISES
      nonempty := by
        suffices : φ 𝕖 = 𝕖
        · exact this
        exact homomorphism_id_map_id φ
      mul_closure := by
        intro a b ha hb
        rw [Set.mem_setOf_eq, ←h, ha, hb, id_op]
      inv_closure := by
        intro a ha
        rw [Set.mem_setOf_eq, homomorphism_id_inv φ, ha, inv_id]

    def Image [Group G] [Group H] (φ : G → H) (h : Homomorphism φ) : Subgroup H where
      carrier := {x : H | ∃ g, φ g = x}
      -- EXERCISES
      nonempty := by
        use 𝕖
        rw [homomorphism_id_map_id φ]
      mul_closure := by
        intro a b ⟨x, hx⟩ ⟨y, hy⟩
        use μ x y
        rw [←h, hx, hy]
      inv_closure := by
        intro a ⟨x, hx⟩
        use ι x
        rw [←hx, homomorphism_id_inv φ]

    def conjugate (g n : G) : G := μ (μ g n) (ι g)

    @[simp]
    theorem conjugate_by_id : conjugate (𝕖 : G) = id := by
      -- EXERCISE
      unfold conjugate
      funext g
      rw [id_op, inv_id, op_id]
      rfl

    @[simp]
    theorem conjugate_id (g : G) : conjugate g 𝕖 = 𝕖 := by
      -- EXERCISE
      unfold conjugate
      rw [op_id, op_inv]

    @[simp]
    theorem conjugate_op (a b : G) : conjugate (μ a b) = conjugate a ∘ conjugate b := by
      funext s
      unfold conjugate
      rw [Function.comp_apply, inv_anticomm]
      simp only [op_assoc]

    def Conjugate (g : G) (S : Set G) : Set G := conjugate g '' S

    -- We define a subgroup to be _normal_ if the subgroup is closed under
    -- conjugation with any element of G.
    def normal (H : Subgroup G) : Prop :=
      ∀ g h : G, h ∈ H → conjugate g h ∈ H

    theorem Trivial_normal : normal (Trivial : Subgroup G) := by
      -- EXERCISE
      intro g h hh
      rw [hh, conjugate_id]
      trivial

    theorem Complete_normal : normal (Complete : Subgroup G) := by
      -- EXERCISE
      intro _ _ _
      trivial

    theorem Kernel_normal (φ : G → G') (h : Homomorphism φ) : normal (Kernel φ h) := by
      -- EXERCISE
      intro g k hk
      suffices : φ (conjugate g k) = 𝕖
      · exact this
      unfold conjugate
      rw [←h, ←h, hk, op_id, h, op_inv, homomorphism_id_map_id φ]

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

    def Center : Subgroup G := Centralizer Set.univ

    theorem normal_normalizer (H : Subgroup G) : normal H ↔ Normalizer H = H := by
      -- EXERCISE
      -- TODO
      apply Iff.intro
      · intro hH
        apply le_antisymm
        · sorry
        sorry
      · sorry

    theorem homomorphism_inj_iff_kernel_trivial [Group G] [Group H] (φ : G → H) (h : Homomorphism φ) :
        Function.Injective φ ↔ Kernel φ h = Trivial := by
      apply Iff.intro
      · intro hinj
        apply le_antisymm
        · intro x hx
          suffices : x = 𝕖
          · exact this
          apply hinj
          rw [homomorphism_id_map_id φ]
          exact hx
        · apply Trivial_smallest
      · intro hk x y hfeq
        -- Need some more homomorphism machinery
        sorry

    theorem homomorphism_surj_iff_image_complete [Group G] [Group H] (φ : G → H) (h : Homomorphism φ) :
        Function.Surjective φ ↔ Image φ h = Complete := by
      apply Iff.intro
      · intro hsurj
        apply le_antisymm
        · apply Complete_largest
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
