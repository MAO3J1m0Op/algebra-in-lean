import «AlgebraInLean».Chapter3.«Sheet1+CHALLENGE»
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

    def Pows (x : G) : Subgroup G where
      carrier := {g : G | ∃ a, gpow x a = g}
      nonempty := by
        use 0
        rw [gpow_zero]
      mul_closure := by
        intro g₁ g₂ ⟨a, ha⟩ ⟨b, hb⟩
        use a + b
        rw [←ha, ←hb, gpow_add]
      inv_closure := by
        intro g ⟨a, ha⟩
        use -a
        have : ∀ i : G, μ i g = 𝕖 → i = ι g := sorry -- inverse unique
        apply this
        rw [←ha, gpow_neg, inv_op]

    theorem Pows_contain_self (x : G) : x ∈ Pows x := by
      use 1
      exact gpow_one x

    noncomputable def Pows_equiv_fin_order (x : G) (h : 0 < order x) : Pows x ≃ Fin (order x) := by
      let φf : Pows x → Fin (order x) := λ ⟨g, hg⟩ ↦ by
        unfold Pows at hg
        dsimp at hg
        set v := Int.toNat (hg.choose % ↑(order x)) with hv
        have hv : v < order x
        · rw [hv, Int.toNat_lt]
          · apply Int.emod_lt_of_pos hg.choose
            rw [Int.ofNat_pos]
            exact h
          · apply Int.emod_nonneg
            rw [Int.natCast_ne_zero_iff_pos]
            exact h
        exact ⟨v, hv⟩
      let φb : Fin (order x) → Pows x := λ ⟨n, hn⟩ ↦ by
        set v := gpow x n
        have hv : v ∈ Pows x := by use n
        exact ⟨v, hv⟩
      apply Equiv.mk φf φb
      · intro ⟨g, hg⟩
        dsimp [φb, φf]
        congr
        rw [Int.toNat_of_nonneg]
        · rw [gpow_mod_order]
          exact hg.choose_spec
        · apply Int.emod_nonneg
          rw [Int.natCast_ne_zero_iff_pos]
          exact h
      · intro ⟨g, hg⟩
        dsimp [φb, φf]
        congr
        sorry
        -- rw [Int.toNat_of_nonneg]
        -- · rw [gpow_mod_order]
        --   exact hg.choose_spec
        -- · apply Int.emod_nonneg
        --   rw [Int.natCast_ne_zero_iff_pos]
        --   exact h
      done

    def gpowMap (x : G) (n : ℤ) : Pows x := ⟨gpow x n, by apply gpow_closure; exact Pows_contain_self x⟩

    def finPowMap (x : G) (n : ℕ) (k : Fin n) : Pows x := gpowMap x k

    theorem finPowMapOrderBijective (x : G) (h : order x ≠ 0) : Function.Bijective (finPowMap x (order x)) := by
      apply And.intro
      · intro ⟨a, ha⟩ ⟨b, hb⟩ heq
        congr
        apply mpow_inj_of_lt_order x
        · exact ha
        · exact hb
        · repeat rw [←gpow_ofNat]
          dsimp [finPowMap, gpowMap] at heq
          rw [Subtype.ext_iff] at heq
          exact heq
      · intro ⟨g, hg⟩
        obtain ⟨a, ha⟩ := hg
        set k := (a % order x).toNat with kdef
        have hk : k < order x
        · rw [kdef]
          rw [Int.toNat_lt]
          · apply Int.emod_lt_of_pos
            apply Ne.lt_of_le
            · symm
              rw [Int.ofNat_ne_zero]
              exact h
            · exact Int.ofNat_zero_le (order x)
          · apply Int.emod_nonneg
            rw [Int.ofNat_ne_zero]
            exact h
        use Fin.mk k hk
        dsimp [finPowMap, gpowMap]
        congr
        rw [kdef, Int.toNat_of_nonneg, ←ha]
        · exact gpow_mod_order x a
        · apply Int.emod_nonneg
          rw [Int.ofNat_ne_zero]
          exact h

    lemma yummy_lemma (x : G) (h : order x ≠ 0) (e : Pows x ≃ Fin n) : n = order x := by
      have : Nat.card (Pows x) = n := Nat.card_eq_of_equiv_fin e
      rw [←this]
      apply Nat.card_eq_of_equiv_fin
      apply Equiv.symm
      apply Equiv.ofBijective (finPowMap x (order x))
      · exact finPowMapOrderBijective x h
      -- have : ∀ a b : Fin n, ∀ α : Type*, (α ≃ Fin a) → (α ≃ Fin b) → a = b := by
      -- apply?

      -- by_cases ho : order x ≠ 0
      -- · have ho : 0 < order x := Nat.zero_lt_of_ne_zero ho
      --   have e' := Pows_equiv_fin_order x ho
      --   have : Fin n ≃ Fin (order x) := (e.symm).trans e'
      --   rw [←Fin.equiv_iff_eq]
      --   use this
      -- · rw [ne_eq, Decidable.not_not] at ho
      --   rw [ho]

      -- by_cases hn : n = 0
      -- · have := e ⟨𝕖, (Pows x).nonempty⟩
      --   rw [hn] at this
      --   obtain ⟨_, h⟩ := this
      --   contradiction
      -- ·
      -- have hf' : ∀ g, e.invFun (f' g) = gpow x (f' g) := by
      --   intro g
      --   dsimp [f']
      --   apply @Exists.choose_spec  (∃ k : Fin n, e.invFun k = gpow x k)
      -- have f : Fin n ≃ Pows x := by
      --   set toFun : Fin n → Pows x := λ k ↦ ⟨gpow x k, gpow_closure x (Pows_contain_self x)⟩
      --   have invProp : ∀ g : Pows x, ∃ k : Fin n, e.invFun k = gpow x k
      --   · intro g
      --     sorry
      --   have invFn : Pows x → Fin n := λ g ↦ Exists.choose (invProp g)
      --   have hInvFn : ∀ g : Pows x, e.invFun (invFn g) = gpow x (invFn g)
      --   · intro g
      --     sorry -- This is terrible
      --     -- apply Exists.choose_spec (invProp g)
      --   -- apply Equiv.mk toFun (Exists.choose invProp)
      --   sorry
      -- sorry


      --     -- Exists.choose
      --     -- let prop := λ k ↦ (h : k < n) → e.invFun ⟨k, h⟩ = gpow x k
      --     -- have this : ∃ k : ℕ, prop k := sorry
      --     -- have _ := Classical.decPred
      --     -- ⟨@Nat.find prop (Classical.decPred prop) this, Nat.find_spec this⟩
      --   left_inv := by
      --     intro k
      --     have x := (invProp (toFun k)).choose_spec
      --     simp at x


      --     apply Exists.choose_spec

      -- }


      -- have ⟨k, hk⟩ : ∃ k : Fin n, mpow x k = 𝕖 := by
      --   sorry
      -- have ⟨k', ⟨hks, hk'⟩⟩ : ∃ k' : Fin n, k' ≠ k ∧ mpow x k' = 𝕖 := by
      --   sorry


      -- have h₁ : n ≤ order x := by

      --   have : ∃ n₀ : ℕ, mpow x n₀ = 𝕖 := by
      --     sorry
      --   have : ∃ n₁ : ℕ, mpow x n₁ = 𝕖 := by
      --     sorry
      -- have h₂ : order x ∣ n := by
      --   rw [←order_divides_iff_mpow_id]


    theorem Pows_order (x : G) : Nat.card (Pows x) = order x := by
      by_cases h : order x ≠ 0
      · apply Nat.card_eq_of_equiv_fin
        apply Pows_equiv_fin_order
        exact Nat.zero_lt_of_ne_zero h
      · rw [ne_eq, Decidable.not_not] at h
        rw [h]
        apply Set.Infinite.card_eq_zero
        unfold Set.Infinite
        by_contra!
        cases this with | @intro n map =>
        have : ∃ i : Fin n, map.symm i = gpow x n
        · have this := map.symm.surjective
          specialize this ⟨gpow x n, by apply gpow_closure; exact Pows_contain_self x⟩
          obtain ⟨a, ha⟩ := this
          use a
          rw [ha]
        obtain ⟨i, hi⟩ := this
        have : ∃ m : Fin n, gpow x m = gpow x n
        · have this := map.surjective
          dsimp [Function.Surjective] at this
          rw [←hi]
          have this' : ∀ g : Pows x, ∃ m : Fin n, gpow x m = g
          · intro g
            have this := (test x n map).surjective
            unfold Function.Surjective at this
            obtain ⟨a, ha⟩ := this g
            use a
            simp [gpowMap] at ha
            rw [←Subtype.val_inj] at ha
            exact ha
          exact this' ↑(map.symm i)
        obtain ⟨m, hm⟩ := this
        have : ↑m ≠ n
        · have ⟨m, hm⟩ := m
          exact Nat.ne_of_lt hm
        absurd this
        rw [←Int.ofNat_inj]
        apply (gpow_inj_iff_order_zero x).mp h hm
      done

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

    theorem Pows_eq_Generate_singleton (x : G) : Pows x = Generate {x} := by
      apply le_antisymm
      · intro g hg
        intro H hH
        rw [Set.singleton_subset_iff] at hH
        obtain ⟨a, ha⟩ := hg
        rw [←ha]
        apply gpow_closure
        exact hH
      · intro g hg
        dsimp [Pows]
        dsimp [Generate] at hg
        have : {x} ⊆ (Pows x).carrier
        · rw [Set.singleton_subset_iff]
          apply Pows_contain_self
        specialize hg (Pows x) this
        obtain ⟨n, hn⟩ := hg
        use n

    def Homomorphism [Group G] [Group G'] (φ : G → G') : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

    def Isomorphic [Group G] [Group G'] (φ : G → G') : Prop := Function.Bijective φ ∧ Homomorphism φ

    def orderCyclicMap (x : G) (n : Cn (order x)) : Generate {x} := by
      apply Subtype.mk (mpow x n.val)
      unfold Generate
      intro H hH
      set n := n.val
      induction n with
      | zero => exact H.nonempty
      | succ n ih =>
        rw [mpow_succ_right]
        apply H.mul_closure
        · exact ih
        · rw [←Set.singleton_subset_iff]
          exact hH
      done

    theorem cyclic_mpow (n : ℕ) (hn : n > 1) [NeZero n] : ∀ x : Cn n, ∃ a : ℕ, x = mpow ⟨1, by linarith⟩ a := by
      intro ⟨x, hx⟩
      use x
      induction x with
      | zero => rfl
      | succ x ih =>
        rw [mpow_succ_right]
        rw [←ih]
        · congr
          rw [Nat.mod_eq_of_lt hx]
        · linarith

    theorem generate_singleton_mpow (x : G) : ∀ a < order x, mpow x a ∈ Generate {x} := by
      intro a
      induction a with
      | zero =>
        intro _
        rw [mpow_zero]
        exact (Generate {x}).nonempty
      | succ n ih =>
        intro _
        specialize ih (by linarith)
        rw [mpow_succ_right]
        apply (Generate {x}).mul_closure
        · exact ih
        · apply Generate_contain_set
          trivial

    theorem generate_singleton_mpow' (x : G) : ∀ g ∈ Generate {x}, ∃ a, mpow x a = g := by
      intro g hg
      sorry

    def cyclicOrderMap (x : G) (x : Generate {x}) : Cn (order x) := by
      apply Fin.mk (sorry)
      sorry

    theorem Generate_singleton_cyclic (x : G) [NeZero (order x)] : ∃ φ : (Cn (order x)) → Generate {x}, Isomorphic φ := by
      use orderCyclicMap x
      apply And.intro
      · apply And.intro
        · intro a b h
          cases a with | mk a ha =>
          cases b with | mk b hb =>
          congr
          simp only [orderCyclicMap, Subtype.mk.injEq] at h
          exact mpow_inj_of_lt_order x a b ha hb h
        · unfold Function.Surjective
          intro fx
          cases fx with | mk fx hfx =>
          sorry
      · sorry
      done

  end Subgroups
end Defs
