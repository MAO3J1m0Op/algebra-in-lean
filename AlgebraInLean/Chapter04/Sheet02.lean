import AlgebraInLean.Chapter04.Sheet01

namespace AlgebraInLean

variable {G : Type*} [Group G] {H : Subgroup G}

theorem fjldskf (a b u v : G) (ha : a ∈ Coset H u) (hb : b ∈ Coset H v)
  : μ a b ∈ Coset H (μ u v) ↔ normal H := by
  apply Iff.intro
  · intro ⟨k, hk⟩ g n hn
    obtain ⟨u', hu'⟩ := ha
    obtain ⟨v', hv'⟩ := hb
    dsimp [Membership.mem]
    rw [←Coset.subgroup_eq_id, Coset.op_repr_repr 𝕖 n]
    · sorry
    · sorry
  · sorry
