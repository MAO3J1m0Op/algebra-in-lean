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
    protected op_id : ∀ a : G, a ⋆ id = a
    protected id_op : ∀ a : G, id ⋆ a = a

  notation:max "𝕖" => Monoid.id

  @[simp]
  theorem op_id [Monoid M] (a : M) : a ⋆ 𝕖 = a := Monoid.op_id a

  @[simp]
  theorem id_op [Monoid M] (a : M) : 𝕖 ⋆ a = a := Monoid.id_op a

  class CommMonoid (G : Type*) extends Monoid G where
    protected comm : ∀ a b : G, a ⋆ b = b ⋆ a

  @[simp]
  theorem comm [CommMonoid M] (a b : M) : a ⋆ b = b ⋆ a := CommMonoid.comm a b

  class Group (G : Type*) extends Monoid G where
    protected inv : G → G
    protected inv_op : ∀ a : G, (inv a) ⋆ a = 𝕖
    -- protected op_inv : ∀ a : G, a ⋆ (inv a) = 𝕖

  -- TODO: solve notational debate
  postfix:1023 "⁻¹" => Group.inv

  @[simp]
  theorem inv_op [Group G] (a : G) : a⁻¹ ⋆ a = 𝕖 := Group.inv_op a

  class AbelianGroup (G : Type*) extends Group G, CommMonoid G

end Defs
