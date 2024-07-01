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

    theorem klein4_2 : HasFinOrder ft 2 := by
      apply And.intro (by linarith)
      apply And.intro
      · rw [mpow_two]
        rfl
      · intro m hm hm₀
        have : m = 1 := Nat.eq_of_le_of_lt_succ hm₀ hm
        rw [this, mpow_one]
        dsimp only [ft, 𝕖, Monoid.id]
        sorry

    theorem HasOrder_nonzero (x : G) : ¬HasFinOrder x 0 := by
      unfold HasFinOrder
      simp

    theorem pos_FinOrder_unique (x : G) (m n : ℕ) (hm : HasFinOrder x m) (hn : HasFinOrder x n) : m = n := by
      wlog hle : m ≤ n
      · have hle : n ≤ m := Nat.le_of_not_ge hle
        symm
        exact this x n m hn hm hle
      unfold HasFinOrder at *
      obtain ⟨_, ⟨_, hn⟩⟩ := hn
      by_cases h : m = n
      · exact h
      have hlt : m < n := Nat.lt_of_le_of_ne hle h
      obtain ⟨hm₀, ⟨hm, _⟩⟩ := hm
      specialize hn m hlt hm₀
      contradiction

    theorem order_smallest (x : G) (n : ℕ) (hn : mpow x n = 𝕖) (hn₀ : 0 < n) (h : ∀ m < n, 0 < m → ¬HasFinOrder x m) : HasFinOrder x n := by
      apply And.intro hn₀
      apply And.intro hn
      intro m hm hm₀
      specialize h m hm hm₀
      set m' := Nat.pred m with hm'
      have hm' : m = Nat.succ m'
      · exact Eq.symm (Nat.sub_one_add_one_eq_of_pos hm₀)
      -- rw [hm'] at hm hm₀ ⊢

      induction m with
      | zero =>
        linarith
        rw [hm'] at hm hm₀
        linarith
      | succ n ih => sorry
      -- have : ∃ m', m = Nat.succ m'
      -- · sorry
      --   -- exact Nat.succ_pred_eq_of_pos hm₀
      -- induction m' with
      -- | zero =>
      --   apply And.intro hm₀
      --   apply And.intro h
      --   intro k hk hk₀
      --   exfalso
      --   linarith
      -- | succ m' ih =>
      --   by_cases hm' : m' ≤ m
      --   · apply And.intro hm₀
      --     apply And.intro h
      --     intro k hk hk₀

      --     -- by_cases hk : mpow x k = 𝕖
      --     -- · sorry
      --     -- · sorry
      --   · linarith
      done

    theorem finite_order (x : G) (n : ℕ) (hn : n > 0) : mpow x n = 𝕖 → ∃ m ≤ n, m ∣ n ∧ HasFinOrder x m := by
      intro h
      by_cases hd : ∃ m < n, HasFinOrder x m
      · obtain ⟨m, hm⟩ := hd
        use m
        apply And.intro (Nat.le_of_succ_le hm.left)
        apply And.intro
        · sorry
        · exact hm.right
      · use n
        apply And.intro (Nat.le_refl n)
        apply And.intro (Nat.dvd_refl n)
        apply And.intro hn
        apply And.intro h

        intro m hm
        simp only [not_exists, not_and] at hd
        specialize hd m hm
        intro hm₀
        contrapose! hd
        apply order_smallest
        · exact hd
        · exact hm₀
        · sorry

    -- noncomputable def order (x : G) : ℕ := Nat.nth (λ n ↦ mpow x n = 𝕖) 0

    -- theorem order_zero_eq_infinite (x : G) : order x = 0 ↔ ∀ n ≠ 0, mpow x n ≠ 𝕖 := by
    --   apply Iff.intro
    --   · intro h n hn
    --     unfold order at h
    --     unfold Nat.nth at h
    --     contrapose! h
    --     split
    --     ·
    --   · sorry

    -- theorem finite_or_infinite (x : G) : HasInfinOrder x ∨ ∃ n, HasFinOrder x n := by
    --   by_cases h : ∃ n > 0, mpow x n = 𝕖
    --   · right
    --     obtain ⟨n, ⟨hngz, hn⟩⟩ := h
    --     apply finite_order at hn
    --     obtain ⟨m, hm⟩ := hn
    --     use m
    --     exact hm.right.right
    --     exact hngz
    --   · left
    --     simp only [not_exists, not_and] at h
    --     exact h

    -- noncomputable def order (x : G) : ℕ :=
    --   have _ := Classical.dec
    --   Or.by_cases (finite_or_infinite x) (λ _ ↦ 0) (λ h ↦ h.choose)

    def order (x : G) : ℕ := sorry

    theorem finite_order' (x : G) (n : ℕ) : mpow x n = 𝕖 ↔ order x ∣ n := sorry

    theorem infinite_order' (x : G) : (∀ n > 0, mpow x n ≠ 𝕖) ↔ order x = 0 := sorry

    theorem mpow_order (x : G) (a b : ℕ) : mpow x a = mpow x b → a % (order x) = b % (order x) := by
      intro h


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
