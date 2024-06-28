import «AlgebraInLean».Chapter3.Sheet1
import Mathlib.Data.Nat.Nth

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

    theorem Generate_contain_set (S : Set G) : S ⊆ Generate S := by
      intro x hx
      unfold Generate
      intro H hS
      apply hS
      exact hx

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

  def HasFinOrder (x : G) (n : ℕ) : Prop := 0 < n ∧ mpow x n = 𝕖 ∧ ∀ m < n, 0 < m → mpow x m ≠ 𝕖

    def HasInfinOrder (x : G) : Prop := ∀ n > 0, mpow x n ≠ 𝕖

    noncomputable def finOrder (x : G) := Nat.nth (λ n ↦ mpow x n = 𝕖) 0

    -- theorem InfinOrder_eq_FinOrder_zero (x : G) : HasInfinOrder x ↔ HasFinOrder x 0 := by
    --   apply Iff.intro
    --   · intro h
    --     sorry

    def Klein4 := Bool × Bool

    instance : AbelianGroup Klein4 where
      op := λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ↦ (xor a₁ b₁, xor a₂ b₂)
      op_assoc := by
        intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
        dsimp only [μ, Magma.op]
        congr 1 <;> apply Bool.xor_assoc
      id := (false, false)
      op_id := by
        intro ⟨a₁, a₂⟩
        dsimp only [μ, Magma.op]
        congr 1 <;> apply Bool.xor_false
      id_op := by
        intro ⟨a₁, a₂⟩
        dsimp only [μ, Magma.op]
        congr 1 <;> apply Bool.false_xor
      inv := id
      inv_op := by
        intro ⟨a₁, a₂⟩
        dsimp only [μ, Magma.op, id]
        congr 1 <;> apply Bool.xor_self
      op_comm := by
        intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
        dsimp only [μ, Magma.op]
        congr 1 <;> apply Bool.xor_comm

    def ft : Klein4 := (false, true)

    def Cn (n : ℕ): Type := Fin n
    /- Fin n already has an add function that automatically takes mod n. This is
    equivalent to a rotation of more than 360° being converted to a rotation of
    less than 360°-/
    def fCn (n : ℕ) : (Cn n) → (Cn n) → (Cn n) := Fin.add
    /- Again we define the inverse function before proving that Cn is a group-/
    def fCn_inv (n : ℕ): (Fin n) → (Fin n) := fun x => -x
    instance {n : ℕ} [hpos : NeZero n]: Defs.Group (Cn n) where
      op := fCn n
      op_assoc := by
        intro a b c
        have h : ∀ (a b c : Fin n), a + b + c = a + (b + c)
        exact fun a b c => add_assoc a b c
        exact h a b c
        done
      /- Elements in Fin n, which is how we are representing Cn, are defined as a
      natural number x, along with a proof that x < n. Fin n also has many of
      the properties we need to show already proven. -/
      id := {val := 0, isLt := Fin.size_pos'}
      /- Try to prove the other group axioms. If you are struggling, similar proofs
      to the proof for op_assoc can work for the other axioms.-/
      op_id := by
        -- sorry
        -- SAMPLE SOLUTION
        intro a
        exact Fin.add_zero a
        -- END OF SAMPLE SOLUTION
      id_op := by
        -- sorry
        -- SAMPLE SOLUTION
        intro a
        have h : ∀ (a : Fin n), 0 + a = a
        exact fun a => Fin.zero_add a
        exact h a
        -- END OF SAMPLE SOLUTION
      inv := fCn_inv n
      inv_op := by
        -- sorry
        -- SAMPLE SOLUTION
        intro a
        have h : ∀ (a : Fin n), -a + a = 0
        exact fun a => neg_add_self a
        exact h a
        -- END OF SAMPLE SOLUTION

    def Homomorphism [Group G] [Group G'] (φ : G → G') : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

    def Isomorphic [Group G] [Group G'] (φ : G → G') : Prop := Function.Bijective φ ∧ Homomorphism φ

    theorem Generate_singleton_cyclic (x : G) [NeZero (order x)] : ∃ φ : (Cn (order x)) → Generate {x}, Isomorphic φ := by
      use λ cn ↦ intro (mpow x cn.val) (by
        unfold Generate
        intro H hH
        set n := cn.val
        induction n with
        | zero => exact H.nonempty
        | succ n ih =>
          rw [mpow_succ]
          apply H.mul_closure
          · exact ih
          · rw [←Set.singleton_subset_iff]
            exact hH
        done
      )
      apply And.intro
      · apply And.intro
        · intro a b h
          dsimp only at h
          sorry

    theorem order_elem_eq_cylic (x : G) : order x = Nat.card (Generate {x}) := by
      by_cases h : Finite (Generate {x})
      · have h : Nat.card (Generate {x}) ≠ 0
        · rw [Nat.card_ne_zero]
          apply And.intro
          · use 𝕖
            exact (Generate {x}).nonempty
          · exact h
        sorry -- Need more cyclic machinery



    -- TODO: discussion of order and cyclic groups

  end Subgroups
end Defs
