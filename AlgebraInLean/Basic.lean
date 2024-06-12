import Mathlib.Tactic

namespace Defs
  class Magma (G : Type*) where
    op : G → G → G

  -- FIXME: is this actually helpful/necessary
  attribute [always_inline] Magma.op

  infixl:75 " ⋆ " => Magma.op

  class Semigroup (G : Type*) extends Magma G where
    protected assoc : ∀ a b c : G, (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)

  @[simp]
  theorem assoc [Semigroup G] (a b c : G) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := Semigroup.assoc a b c

  class Monoid (G : Type*) extends Semigroup G where
    protected id : G
    protected mul_id : ∀ a : G, a ⋆ id = a
    protected id_mul : ∀ a : G, id ⋆ a = a

  notation:max "𝕖" => Monoid.id

  @[simp]
  theorem mul_id [Monoid M] (a : M) : a ⋆ 𝕖 = a := Monoid.mul_id a

  @[simp]
  theorem id_mul [Monoid M] (a : M) : 𝕖 ⋆ a = a := Monoid.id_mul a

  class CommMonoid (G : Type*) extends Monoid G where
    protected comm : ∀ a b : G, a ⋆ b = b ⋆ a

  @[simp]
  theorem comm [CommMonoid M] (a b : M) : a ⋆ b = b ⋆ a := CommMonoid.comm a b

  class Group (G : Type*) extends Monoid G where
    protected inv : G → G
    protected inv_mul : ∀ a : G, (inv a) ⋆ a = 𝕖
    -- protected mul_inv : ∀ a : G, a ⋆ (inv a) = 𝕖

  -- TODO: solve notational debate
  postfix:1023 "⁻¹" => Group.inv

  @[simp]
  theorem inv_mul [Group G] (a : G) : a⁻¹ ⋆ a = 𝕖 := Group.inv_mul a

  @[simp]
  theorem mul_inv [Group G] (a : G) : a ⋆ a⁻¹ = 𝕖 := by
    -- apply Group.cancel_left a⁻¹
    -- rw [←assoc, inv_mul, mul_id, id_mul]
    -- done
    sorry

  class AbelianGroup (G : Type*) extends Group G, CommMonoid G

end Defs
