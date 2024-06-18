import «AlgebraInLean».Chapter3.Sheet1

namespace Defs
  namespace Subgroups

    instance [Group G] : LE (Subgroup G) := ⟨λ H K ↦ H.carrier ⊆ K.carrier⟩

    theorem Trivial_smallest [Group G] (H : Subgroup G) : Trivial ≤ H := by
      -- EXERCISE
      intro e he
      rw [he]
      exact H.nonempty

    theorem Complete_largest [Group G] (H : Subgroup G) : H ≤ Complete := by
      -- EXERCISE
      intro x _
      trivial

    theorem le_refl [Group G] (H : Subgroup G) : H ≤ H := by
      -- If `unfold` does not fully expand the definition as desired, try using
      -- it as a lemma in `dsimp`.
      dsimp only [LE.le]
      trivial

    theorem le_trans [Group G] (H₁ H₂ H₃ : Subgroup G) : H₁ ≤ H₂ → H₂ ≤ H₃ → H₁ ≤ H₃ := by
      -- EXERCISE
      dsimp only [LE.le] at *
      intro h12 h23
      intro x h1_x
      apply h23
      apply h12
      exact h1_x

    theorem le_antisymm [Group G] (H K : Subgroup G) : H ≤ K → K ≤ H → H = K := by
      intro hH hK
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

    def Intersect [Group G] (H K : Subgroup G) : Subgroup G where
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
    instance [Group G] : Inter (Subgroup G) := ⟨Intersect⟩

    theorem inter_comm [Group G] (H K : Subgroup G) : H ∩ K = K ∩ H := by
      dsimp only [Inter.inter, Intersect]
      suffices : H.carrier ∩ K.carrier = K.carrier ∩ H.carrier
      · congr
      exact Set.inter_comm H.carrier K.carrier

    theorem inter_assoc [Group G] (H₁ H₂ H₃ : Subgroup G) : (H₁ ∩ H₂) ∩ H₃ = H₁ ∩ (H₂ ∩ H₃) := by
      simp only [Inter.inter, Intersect]
      suffices : (H₁.carrier ∩ H₂.carrier) ∩ H₃.carrier = H₁.carrier ∩ (H₂.carrier ∩ H₃.carrier)
      · congr
      exact Set.inter_assoc H₁.carrier H₂.carrier H₃.carrier

  end Subgroups
end Defs