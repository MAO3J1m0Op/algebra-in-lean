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

end Defs
