import AlgebraInLean.Chapter03.Sheet05

namespace AlgebraInLean

variable {G : Type*} [Group G]

def Coset (H : Subgroup G) (a : G) : Set G := μ a '' H

variable {H : Subgroup G}

theorem Coset.subgroup_eq_id : Coset H (𝕖 : G) = H := by
  ext x
  apply Iff.intro
  · intro hx
    obtain ⟨a, ha⟩ := hx
    rw [←ha.right, id_op]
    exact ha.left
  · intro hx
    use x
    apply And.intro
    · exact hx
    · rw [id_op]

variable {H : Subgroup G}

theorem Coset.mem_def (u a : G) : a ∈ Coset H u ↔ ∃ n ∈ H, μ u n = a := Eq.to_iff rfl

theorem Coset.mem_refl (a : G) : a ∈ Coset H a := by
  rw [Coset.mem_def]
  use 𝕖
  apply And.intro
  · exact H.has_id
  · rw [op_id]

theorem Coset.mem_repr (u v : G) (hv : v ∈ Coset H u) : Coset H u = Coset H v := by
  obtain ⟨n, hn⟩ := hv
  ext x
  apply Iff.intro
  · intro ⟨n', hn'⟩
    use μ (ι n) n'
    apply And.intro
    · exact H.mul_closure (H.inv_closure hn.left) hn'.left
    · rw [←hn.right, ←hn'.right, op_assoc u, ←op_assoc n, op_inv, id_op]
  · intro ⟨n', hn'⟩
    use μ n n'
    apply And.intro
    · exact H.mul_closure hn.left hn'.left
    · rw [←hn'.right, ←hn.right, op_assoc]

theorem Coset.op_repr_repr (a n : G) (hn : n ∈ H) : Coset H a = Coset H (μ a n) := by
  apply Coset.mem_repr
  use n
  trivial

theorem coset_mem_op_refl (a n : G) : n ∈ H → μ a n ∈ Coset H a := by
  intro hn
  use n
  apply And.intro hn rfl

theorem Coset.op_closure (a u n : G) (hn : n ∈ H) (hu : u ∈ Coset H a) : μ u n ∈ Coset H a := by
  obtain ⟨n', hn'⟩ := hu
  rw [←hn'.right]
  use μ n' n
  apply And.intro
  · exact H.mul_closure hn'.left hn
  · rw [op_assoc]

theorem coset_mem_def (u v n : G) : n ∈ H → v ∈ Coset H u → μ v n ∈ Coset H u := by
  intro hn ⟨vn, hvn⟩
  rw [←hvn.right, op_assoc]
  apply coset_mem_op_refl
  apply H.mul_closure
  · exact hvn.left
  · exact hn

theorem coset_mem_symm (u v : G) : u ∈ Coset H v → v ∈ Coset H u := by
  intro hu
  obtain ⟨n, hn⟩ := hu
  use ι n
  apply And.intro
  · exact H.inv_closure hn.left
  · rw [←hn.right, op_assoc, op_inv, op_id]

theorem coset_eq_iff_mem_symm (u v : G) : Coset H u = Coset H v ↔ u ∈ Coset H v := by
  apply Iff.intro
  · intro heq
    rw [←heq]
    exact Coset.mem_refl u
  · intro hu
    symm
    apply Coset.mem_repr
    exact hu

theorem coset_eq_of_share_mem (a u v : G) (ha : a ∈ (Coset H u) ∩ (Coset H v))
  : Coset H u = Coset H v := by
  obtain ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ := ha
  apply Coset.mem_repr
  use μ u' (ι v')
  apply And.intro
  · exact H.mul_closure hu'.left (H.inv_closure hv'.left)
  · rw [←op_assoc, hu'.right, ←hv'.right, op_assoc, op_inv, op_id]

theorem coset_eq_iff_NAME_TBD (u v : G) : Coset H u = Coset H v ↔ μ u (ι v) ∈ H := by
  apply Iff.intro
  · intro heq
    sorry
  · intro h
    ext x
    apply Iff.intro
    · intro ⟨a, ha⟩
      sorry
    · sorry

theorem id_coset_of_mul_closure (a u v : G)
  (h : u ∈ Coset H a → v ∈ Coset H a → μ u v ∈ Coset H a)
  : Coset H a = Coset H 𝕖 := by
    symm
    rw [coset_eq_iff_mem_symm]
    sorry

theorem id_coset_of_inv_closure (a u : G) (h : u ∈ Coset H a → ι u ∈ Coset H a)
  : Coset H a = Coset H 𝕖 := by
    sorry

structure Partition (α : Type*) where
  carrier : Set (Set α)
  independent : ∀ (S T : Set α), S ∈ carrier → T ∈ carrier → S ≠ T → S ∩ T = ∅
  complete : ∀ (a : α), ∃ S ∈ carrier, a ∈ S

instance {α : Type*} : Coe (Partition α) (Set (Set α)) := ⟨λ H ↦ H.carrier⟩

instance {α : Type*} : CoeSort (Partition α) (Type _) := ⟨λ H ↦ H.carrier⟩

attribute [coe] Partition.carrier

def cosetPartition (H : Subgroup G) : Partition G where
  carrier := Coset H '' Set.univ
  independent := by
    intro S T ⟨u, ⟨_, hu⟩⟩ ⟨v, ⟨_, hv⟩⟩ hne
    rw [←hu, ←hv]
    contrapose! hne
    rw [←hu, ←hv]
    obtain ⟨a, ha⟩ := hne
    apply coset_eq_of_share_mem
    exact ha
  complete := by
    intro a
    use Coset H a
    apply And.intro
    · exact Set.mem_image_of_mem (Coset H) trivial
    · exact Coset.mem_refl a

noncomputable def Index (H : Subgroup G) : ℕ := Nat.card (cosetPartition H).carrier

theorem Index_nonempty [Finite G] : Index H ≠ 0 := by
  unfold Index
  rw [Nat.card_ne_zero]
  apply And.intro
  · use Coset H 𝕖
    use 𝕖
    trivial
  · exact Finite.Set.finite_image Set.univ (Coset H)

theorem Coset_card (a : G) : Nat.card (Coset H a) = Nat.card H := by
  unfold Coset
  apply Nat.card_image_of_injective
  intro a b heq
  sorry -- op_left_cancel

theorem lagranges [Fintype G] [Fintype H] : Nat.card H ∣ Nat.card G := by
  rw [←Nat.mod_add_div (Nat.card G) (Nat.card H)]
  by_contra! h
  sorry

theorem better_lagranges : Nat.card H * Index H = Nat.card G := by
  by_cases h : Nat.card H ≠ 0
  · suffices : Nat.card H = Nat.card G / Index H
    · rw [←@Nat.div_left_inj _ _ (Index H), Nat.mul_div_assoc, Nat.div_self, Nat.mul_one]
      · exact this
      · suffices : Index H ≠ 0
        · exact Nat.zero_lt_of_ne_zero this
        sorry
      · sorry
      · sorry
      · sorry
    sorry
  · sorry
