import «AlgebraInLean».Chapter3.Sheet1

namespace Defs
  namespace Subgroups

    section Mpow

    def mpow {M : Type*} [Monoid M] (x : M) : ℕ → M
    | Nat.zero => 𝕖
    | Nat.succ n => μ (mpow x n) x

    variable {M : Type*} [Monoid M] (x : M) (m n : ℕ)

    @[simp]
    theorem mpow_zero : mpow x 0 = 𝕖 := rfl

    @[simp]
    theorem mpow_one : mpow x 1 = x := by
      rw [mpow, mpow_zero, id_op]

    theorem mpow_two : mpow x 2 = μ x x := by
      rw [mpow, mpow_one]

    theorem mpow_succ_right : mpow x (n+1) = μ (mpow x n) x := rfl

    theorem mpow_succ_left : mpow x (n+1) = μ x (mpow x n) := by
      induction n with
      | zero => rw [zero_add, mpow_one, mpow_zero, op_id]
      | succ n ih =>
        rw [mpow_succ_right]
        nth_rw 2 [mpow_succ_right]
        rw [ih, op_assoc]

    theorem mpow_add : μ (mpow x m) (mpow x n) = mpow x (m + n) := by
      induction n with
      | zero => rw [mpow_zero, op_id, Nat.add_zero]
      | succ n ih =>
        rw [←Nat.add_assoc, mpow_succ_right, mpow_succ_right, ←op_assoc, ih]

    theorem mpow_mul : mpow x (m * n) = mpow (mpow x m) n := by
      induction n with
      | zero =>
        rw [mul_zero, mpow_zero, mpow_zero]
      | succ n ih =>
        simp_rw [Nat.mul_succ, ←mpow_add, ih, mpow_one]
      done

    @[simp]
    theorem mpow_id : mpow 𝕖 n = (𝕖 : M) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [mpow_succ_right, ih, op_id]
      done

    end Mpow

    section MonoidOrder

    noncomputable def order [Monoid M] (x : M) : ℕ := by
      classical exact if h : ∃ (n : ℕ), n ≠ 0 ∧ mpow x n = 𝕖 then Nat.find h else 0

    variable {M : Type*} [Monoid M] (x : M) (m n : ℕ)

    theorem mpow_order : mpow x (order x) = 𝕖 := by
      set n := order x with hn
      dsimp [order] at hn
      split_ifs at hn with h <;> rw [hn]
      · classical exact (Nat.find_spec h).right
      · rfl
      done

    theorem mpow_mod_order : mpow x (m % order x) = mpow x m := by
      set n := order x
      nth_rw 2 [←Nat.mod_add_div m n]
      rw [←mpow_add, mpow_mul, mpow_order, mpow_id, op_id]
      done

    theorem order_divides_iff_mpow_id : mpow x m = 𝕖 ↔ order x ∣ m := by
      apply Iff.intro
      · intro hm
        by_cases hm0 : m = 0
        · use 0
          rw [mul_zero, hm0]
        · set n := order x with hn
          dsimp [order] at hn
          split_ifs at hn with h
          · by_contra hnm
            have : m % n < n
            · apply Nat.mod_lt
              rw [hn, GT.gt, pos_iff_ne_zero]
              classical exact (Nat.find_spec h).left
            · nth_rw 2 [hn] at this
              classical apply Nat.find_min h this
              constructor
              · rw [←Nat.dvd_iff_mod_eq_zero]
                exact hnm
              · rw [mpow_mod_order, hm]
          · exfalso
            apply h
            use m
      · rintro ⟨k, rfl⟩
        rw [mpow_mul, mpow_order, mpow_id]
      done

    lemma mpow_inj_of_lt_order (hm : m < order x) (hn : n < order x) : mpow x m = mpow x n → m = n := by
      intro h
      wlog hmn : m ≤ n
      · symm
        exact this x n m hn hm (Eq.symm h) (Nat.le_of_not_ge hmn)
      obtain ⟨k, hk⟩ := Nat.le.dest hmn
      suffices : k = 0
      · rw [this, add_zero] at hk
        exact hk
      apply Nat.eq_zero_of_dvd_of_lt
      · rw [←order_divides_iff_mpow_id x]
        have op_cancel_left : ∀ a u v : M, μ a u = μ a v → u = v := sorry
        apply op_cancel_left (mpow x m)
        rw [op_id, mpow_add, hk]
        exact Eq.symm h
      · rw [←hk] at hn
        linarith
      done

    theorem mod_order_eq_of_mpow_eq (h₀ : order x ≠ 0) : mpow x m = mpow x n → m % (order x) = n % (order x) := by
      intro h
      apply mpow_inj_of_lt_order x (m % order x) (n % order x)
      · apply Nat.mod_lt
        exact Nat.zero_lt_of_ne_zero h₀
      · apply Nat.mod_lt
        exact Nat.zero_lt_of_ne_zero h₀
      · repeat rw [mpow_mod_order]
        exact h
      done


  end MonoidOrder

  section Gpow

    def gpow {G : Type*} [Group G] (x : G) : ℤ → G
    | Int.ofNat n => mpow x n
    | Int.negSucc n => ι (μ (mpow x n) x)

    variable {G : Type*} [Group G] (x : G)

    lemma gpow_ofNat (n : ℕ) : gpow x ↑n = mpow x n := rfl

    @[simp]
    lemma gpow_zero : gpow x 0 = 𝕖 := rfl

    @[simp]
    lemma gpow_one : gpow x 1 = x := by
      rw [←Int.ofNat_one, gpow_ofNat, mpow_one]

    lemma gpow_two : gpow x 2 = μ x x := by
      rw [←Int.ofNat_two, gpow_ofNat, mpow_two]

    lemma gpow_negSucc (n : ℕ) : gpow x (Int.negSucc n) = ι (μ (mpow x n) x) := rfl

    lemma gpow_neg_mpow (n : ℕ) : gpow x (-n) = ι (mpow x n) := by
      cases n with
      | zero =>
        rw [Int.ofNat_zero, Int.neg_zero, gpow_zero, mpow_zero, inv_id]
      | succ n =>
        have : -↑(n + 1) = Int.negSucc n := rfl
        rw [this, gpow_negSucc, ←mpow_succ_right, mpow_succ_left]

    @[simp]
    lemma gpow_neg_one : gpow x (-1) = ι x := by
      rw [←Int.ofNat_one, gpow_neg_mpow, mpow_one]

    lemma gpow_neg (n : ℤ) : gpow x (-n) = ι (gpow x n) := by
      induction n using Int.induction_on with
      | hz => simp [inv_id]
      | hp n ih =>
        rw [←Int.cast_one]
        sorry
      | hn n ih => sorry

    @[simp]
    lemma gpow_succ (n : ℤ) : gpow x (n + 1) = μ (gpow x n) x := by
      induction n using Int.induction_on with
      | hz => rfl
      | hp n _ =>
        repeat rw [←Int.ofNat_one]
        repeat rw [Int.ofNat_add_out]
        repeat rw [gpow_ofNat]
        rfl
      | hn n _ =>
        sorry

    lemma gpow_pred (n : ℤ) : μ (gpow x n) (ι x) = gpow x (n-1) := by
      induction n using Int.induction_on with
      | hz => simp only [gpow_zero, id_op, zero_sub, gpow_neg_one]
      | hp n _ =>
        rw [gpow_succ, gpow_ofNat, op_assoc, op_inv, op_id]
        rw [add_sub_cancel_right, gpow_ofNat]
      | hn n _ =>
        sorry

    @[simp]
    lemma gpow_add (m n : ℤ) : μ (gpow x m) (gpow x n) = gpow x (m + n) := by
      sorry

    @[simp]
    lemma gpow_sub (m n : ℤ) : μ (gpow x m) (ι (gpow x n)) = gpow x (m - n) := by
      rw [sub_eq_add_neg, ←gpow_add, gpow_neg]

    @[simp]
    lemma gpow_mul (m n : ℤ) : gpow x (m * n) = gpow (gpow x m) n := by
      sorry

    theorem gpow_closure {H : Subgroup G} : x ∈ H → gpow x n ∈ H := by
      intro h
      induction n using Int.induction_on with
      | hz => exact H.nonempty
      | hp n ih =>
        rw [gpow_succ]
        apply H.mul_closure
        · exact ih
        · exact h
      | hn n ih =>
        rw [←gpow_pred, gpow_neg]
        apply H.mul_closure
        · rw [←gpow_neg]
          exact ih
        · apply H.inv_closure
          exact h
      done

    end Gpow

    section GroupOrder

    variable {G : Type*} [Group G] (x : G)

    theorem gpow_order : gpow x (order x) = 𝕖 := by
      rw [gpow_ofNat, mpow_order]

    theorem gpow_mod_order (n : ℤ): gpow x (n % order x) = gpow x n := by
      cases n with
      | ofNat n =>
        have : (n : ℤ) % (↑(order x)) = (n % order x : ℕ) := rfl
        rw [Int.ofNat_eq_coe, this, gpow_ofNat, gpow_ofNat, mpow_mod_order]
      | negSucc n =>
        sorry

    theorem gpow_inj_iff_order_zero : order x = 0 ↔ (gpow x m = gpow x n → m = n) := by
      sorry

    theorem mod_order_eq_of_gpow_eq : gpow x m = gpow x n → m % (order x) = n % (order x) := by
      sorry

    end GroupOrder

  end Subgroups
end Defs
