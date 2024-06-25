import «AlgebraInLean».Chapter3.Sheet1

namespace Defs
  namespace Subgroups

    variable {G : Type*} [Group G]

    instance : PartialOrder (Subgroup G) where
      le H K := H.carrier ⊆ K.carrier
      le_refl := by
        intro H
        -- If `unfold` does not fully expand the definition as desired, try using
        -- it as a lemma in `dsimp`.
        dsimp only [LE.le]
        trivial
      le_trans := by
        -- EXERCISE
        intro H₁ H₂ H₃ h12 h23 hx h1_x
        dsimp only [LE.le] at *
        apply h23
        apply h12
        exact h1_x
      le_antisymm := by
        intro H K hH hK
        obtain ⟨H_carrier,_,_,_⟩ := H
        obtain ⟨K_carrier,_,_,_⟩ := K
        congr
        ext x
        apply Iff.intro
        · intro hx
          apply hH
          exact hx
        · intro hx
          apply hK
          exact hx

    theorem Minimal_smallest (H : Subgroup G) : Minimal ≤ H := by
      -- EXERCISE
      intro e he
      rw [he]
      exact H.nonempty

    theorem Maximal_largest (H : Subgroup G) : H ≤ Maximal := by
      -- EXERCISE
      intro x _
      trivial

    def Intersect (H K : Subgroup G) : Subgroup G where
      carrier := H ∩ K
      -- EXERCISES
      nonempty := by
        exact And.intro H.nonempty K.nonempty
      mul_closure := by
        intro a b ha hb
        apply And.intro
        · exact H.mul_closure a b ha.left hb.left
        · exact K.mul_closure a b ha.right hb.right
      inv_closure := by
        intro a ha
        apply And.intro
        · exact H.inv_closure a ha.left
        · exact K.inv_closure a ha.right

    -- TODO: Other symbols : ∩, ⊓, ∧?
    instance : Inter (Subgroup G) := ⟨Intersect⟩

    theorem inter_comm (H K : Subgroup G) : H ∩ K = K ∩ H := by
      dsimp only [Inter.inter, Intersect]
      suffices : H.carrier ∩ K.carrier = K.carrier ∩ H.carrier
      · congr
      exact Set.inter_comm H.carrier K.carrier

    theorem inter_assoc (H₁ H₂ H₃ : Subgroup G) : (H₁ ∩ H₂) ∩ H₃ = H₁ ∩ (H₂ ∩ H₃) := by
      simp only [Inter.inter, Intersect]
      suffices : (H₁.carrier ∩ H₂.carrier) ∩ H₃.carrier = H₁.carrier ∩ (H₂.carrier ∩ H₃.carrier)
      · congr
      exact Set.inter_assoc H₁.carrier H₂.carrier H₃.carrier

    -- Here, we prove that H ∩ K is the "greatest lower bound", or the largest
    -- subgroup that is smaller than both H and K.
    theorem le_intersect_self (H K : Subgroup G): H ∩ K ≤ H := by
      -- EXERCISE
      intro g hg
      exact hg.left

    theorem nameTODO (H K I : Subgroup G) : I ≤ H ∧ H ∩ K ≤ I → I = H ∩ K ∨ I = H := by
      -- EXERCISE
      intro ⟨h₁, h₂⟩
      sorry --

    -- Given a group G and a subset of that group, S, the subgroup generated
    -- by S is the smallest order subgroup H ≤ G such that S ⊆ H. We show that
    -- such a subset H which contains S is a subgroup in the example below.
    def Generate (S : Set G) : Subgroup G where
      carrier := {g : G | ∀ H : Subgroup G, S ⊆ H → g ∈ H}
      -- EXERCISE
      nonempty := by
        intro H _
        exact H.nonempty
      mul_closure := by
        dsimp at *
        intro a b ha hb H hH
        apply H.mul_closure
        · exact ha H hH
        · exact hb H hH
      inv_closure := by
        intro a ha H hH
        apply H.inv_closure
        exact ha H hH

    theorem Generate_empty : Generate ∅ = (Minimal : Subgroup G) := by
      -- EXERCISE
      apply le_antisymm
      · intro g hg
        unfold Generate at hg
        dsimp only at hg
        specialize hg Minimal
        apply hg
        apply Set.empty_subset
      · apply Minimal_smallest

    theorem Generate_self_eq_self (H : Subgroup G) : Generate H = H := by
      -- EXERCISE
      apply le_antisymm
      · intro g hg
        specialize hg H
        apply hg
        rfl
      · intro g hg
        intro K hK
        apply hK
        exact hg

      theorem Generate_lub (S : Set G) (H : Subgroup G) : S ⊆ H ∧ H ≤ Generate S → H = Generate S := by
        -- EXERCISE
        intro ⟨hl, hr⟩
        apply le_antisymm
        · exact hr
        · intro g hg
          apply hg H
          exact hl

      def mpow [Monoid M] (x : M) : ℕ → M
    | Nat.zero => 𝕖
    | Nat.succ n => μ (mpow x n) x

    @[simp]
    theorem mpow_zero [Monoid M] (x : M) : mpow x 0 = 𝕖 := rfl

    @[simp]
    theorem mpow_one [Monoid M] (x : M) : mpow x 1 = x := by
      rw [mpow, mpow_zero, id_op]

    theorem mpow_two [Monoid M] (x : M) : mpow x 2 = μ x x := by
      rw [mpow, mpow_one]

    @[simp]
    theorem mpow_succ [Monoid M] (x : M) (n : ℕ) : mpow x (n+1) = μ (mpow x n) x := rfl

    @[simp]
    theorem mpow_add [Monoid M] (x : M) (m n : ℕ) : μ (mpow x m) (mpow x n) = mpow x (m + n) := by
      induction n with
      | zero => rw [mpow_zero, op_id, Nat.add_zero]
      | succ n ih =>
        rw [←Nat.add_assoc, mpow_succ, mpow_succ, ←op_assoc, ih]

  end Subgroups
end Defs
