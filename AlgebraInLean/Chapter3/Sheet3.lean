import «AlgebraInLean».Chapter3.Sheet2

namespace Defs
  namespace Subgroups

    variable {G G' : Type*} [Group G] [Group G']

    -- TODO: will be imported
    def Homomorphism (φ : G → G') : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

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

    def conjugate (n g : G) : G := μ (μ n g) (ι g)

    -- We define a subgroup to be _normal_ if the subgroup is closed under
    -- conjugation with any element of G.
    -- TODO: include conjugation in the definition?
    def normal (H : Subgroup G) : Prop :=
      ∀ g h : G, h ∈ H → μ (μ g h) (ι g) ∈ H

    theorem Trivial_normal : normal (Trivial : Subgroup G) := by
      -- EXERCISE
      intro g h hh
      rw [hh, op_id, op_inv]
      trivial

    theorem Complete_normal : normal (Complete : Subgroup G) := by
      -- EXERCISE
      intro _ _ _
      trivial

    theorem Kernel_normal (φ : G → G') (h : Homomorphism φ) : normal (Kernel φ h) := by
      -- EXERCISE
      intro g k hk
      suffices : φ (μ (μ g k) (ι g)) = 𝕖
      · exact this
      rw [←h, ←h, hk, op_id, h, op_inv, homomorphism_id_map_id φ]

    def Normalizer (S : Set G) : Subgroup G where
      carrier := {g | ∀ s ∈ S, μ (μ g s) (ι g) = s}
      nonempty := by
        intro s hs
        rw [id_op, inv_id, op_id]
      mul_closure := by
        intro a b ha hb s hs
        rw [inv_anticomm]
        rw [op_assoc, op_assoc a, ←op_assoc s, ←op_assoc b, ←op_assoc b]
        rw [hb s hs, ←op_assoc, ha s hs]
      inv_closure := by
        intro a ha b hb
        have inv_inv_eq_self : ∀ g : G, ι (ι g) = g := by
          intro x
          have h1 : ∀ g : G, μ (ι (ι g)) (ι g) = 𝕖 := by
            intro y
            rw[inv_op]
          have h2 : ∀ g : G, μ (g) (ι g) = 𝕖 := by
            intro z
            rw[op_inv] --ONLY VALID WITH op_inv PROOF
          have h1_x := h1 x
          have h2_x := h2 x
          rw [← h2_x] at h1_x
          sorry -- FIXME do we have a uniqe inverse theorem?
        have h3_a := inv_inv_eq_self a
        rw [h3_a]
        have h3 : μ (μ a b) (ι a) = b → μ (μ (ι a) b) a = b := by
          intro ht
          have hp : μ (μ a b) (ι a) = b → μ (ι a) (μ (μ a b) (ι a)) = μ (ι a) b := by
            intro hu
            rw [hu]
          apply hp at ht
          rw [op_assoc, ← op_assoc, inv_op, id_op] at ht
          have hq : μ b (ι a) = μ (ι a) b → μ (μ b (ι a)) a = μ (μ (ι a) b) a := by
            intro hu
            rw [hu]
          apply hq at ht
          rw [op_assoc, inv_op, op_id] at ht
          symm
          exact ht
        rw [h3]
        have ha_b := ha b
        apply ha_b at hb
        exact hb

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

    theorem normal_normalizer (H : Subgroup G) : normal H ↔ Normalizer Set.univ = H := by
      -- EXERCISE
      -- TODO
      sorry

    theorem homomorphism_inj_iff_kernel_trivial [Group G] [Group H] (φ : G → H) (h : Homomorphism φ) :
        Function.Injective φ ↔ Kernel φ h = Trivial := by
      apply Iff.intro
      · intro hinj
        apply le_antisymm
        · intro x hx
          suffices : x = 𝕖
          · exact this
          apply hinj
          have : φ 𝕖 = 𝕖 := sorry
          rw [this]
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
