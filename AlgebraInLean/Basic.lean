import Mathlib.Tactic

namespace Defs
  class Magma (G : Type*) where
    op : G → G → G

  def μ [Magma G] : G → G → G := Magma.op

  class Semigroup (G : Type*) extends Magma G where
    protected op_assoc : ∀ a b c : G, μ (μ a b) c = μ a (μ b c)

  @[simp]
  theorem op_assoc [Semigroup G] (a b c : G) : μ (μ a b) c = μ a (μ b c) := Semigroup.op_assoc a b c

  class Monoid (G : Type*) extends Semigroup G where
    protected id : G
    protected op_id : ∀ a : G, μ a id = a
    protected id_op : ∀ a : G, μ id a = a

  def 𝕖 [Monoid G] : G := Monoid.id

  @[simp]
  theorem op_id [Monoid M] (a : M) : μ a 𝕖 = a := Monoid.op_id a

  @[simp]
  theorem id_op [Monoid M] (a : M) : μ 𝕖 a = a := Monoid.id_op a

  class CommMonoid (G : Type*) extends Monoid G where
    protected op_comm : ∀ a b : G, μ a b = μ b a

  @[simp]
  theorem op_comm [CommMonoid M] (a b : M) : μ a b = μ b a := CommMonoid.op_comm a b

  class Group (G : Type*) extends Monoid G where
    protected inv : G → G
    protected inv_op : ∀ a : G, μ (inv a) a = 𝕖
    -- protected op_inv : ∀ a : G, μ a (inv a) = 𝕖

  def ι [Group G] : G → G := Group.inv

  @[simp]
  theorem inv_op [Group G] (a : G) : μ (ι a) a = 𝕖 := Group.inv_op a

  @[simp]
  theorem op_inv [Group G] (a : G) : μ a (ι a) = 𝕖 := sorry

  theorem inv_id [Group G] : ι 𝕖 = (𝕖 : G) := sorry

  theorem inv_anticomm [Group G] (a b : G) : ι (μ a b) = μ (ι b) (ι a) := sorry

  class AbelianGroup (G : Type*) extends Group G, CommMonoid G

  namespace Subgroups

    structure Subgroup (G : Type*) [Group G] where
      carrier : Set G
      nonempty : 𝕖 ∈ carrier
      mul_closure : ∀ a b, a ∈ carrier → b ∈ carrier → μ a b ∈ carrier
      inv_closure : ∀ a : G, a ∈ carrier → ι a ∈ carrier

    instance [Group G] : Coe (Subgroup G) (Set G) := ⟨λ H ↦ H.carrier⟩

    instance {G : Type u} [Group G] : CoeSort (Subgroup G) (Type u) := ⟨λ H ↦ H.carrier⟩

    def Centralizer [Group G] (S : Set G) : Subgroup G where
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

    def conjugate [Group G] (n g : G) : G := μ (μ n g) (ι g)

    def Normalizer [Group G] (S : Set G) : Subgroup G where
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
        sorry

    structure NormalSubgroup (G : Type*) [Group G] extends Subgroup G where
      normal : ∀ g h : G, h ∈ carrier → μ (μ g h) (ι g) = h
      -- normal : (Normalizer carrier).carrier = Set.univ

    variable {G : Type*} [Group G]

    def Trivial : NormalSubgroup G where
      carrier := {𝕖}
      nonempty := by trivial
      mul_closure := by
        intro a b ha hb
        rw [ha, hb, id_op]
        trivial
      inv_closure := by
        intro a ha
        rw [ha, inv_id]
        trivial
      normal := by
        -- ext g
        -- apply Iff.intro <;> intros
        -- · trivial
        -- · intro s hs
        --   rw [hs, op_id, op_inv]
        intro g h hh
        rw [hh, op_id, op_inv]

    def Complete : Subgroup G where
      carrier := Set.univ
      nonempty := trivial
      mul_closure a b ha hb := trivial
      inv_closure a ha := trivial

    theorem foldml_append [Monoid M] (xs ys : List M)
        : List.foldl μ 𝕖 (xs ++ ys) = μ (List.foldl μ 𝕖 xs) (List.foldl μ 𝕖 ys) := by
      sorry

    def Generate (S : Set G) : Subgroup G where
      carrier := {g | ∃ xs : List {s : G // s ∈ S ∨ ι s ∈ S}, List.foldl μ (𝕖 : G) xs = g}
      nonempty := Exists.intro [] rfl
      mul_closure := by
        dsimp at *
        intro a b ⟨as, has⟩ ⟨bs, hbs⟩
        use as ++ bs
        sorry
      inv_closure :=
      sorry

    def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

    def Kernel [Group G] [Group H] (φ : G → H) (h : Homomorphism φ) : NormalSubgroup G where
      carrier := {g | φ g = 𝕖}
      nonempty := sorry
      mul_closure := sorry
      inv_closure := sorry
      normal := sorry

  end Subgroups

end Defs
