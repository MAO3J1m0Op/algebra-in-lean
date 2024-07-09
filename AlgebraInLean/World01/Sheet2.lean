import AlgebraInLean.World01.Sheet1

namespace AlgebraInLean

/- Groups aren't the only important structures in algebra. By adding or subtracting certain
properties from our definition, we create structures with different properties. -/

/- The simplest structure in algebra is a magma, which only requires a closed operation. -/
class Magma (G : Type*) where
  op : G → G → G

def μ [Magma G] : G → G → G := Magma.op

/- The next structure is a semigroup, which is a magma with the associative property. The extends
keyword means that a semigroup has all the properties of a magma. -/
class Semigroup (G : Type*) extends Magma G where
  protected op_assoc : ∀ a b c : G, μ (μ a b) c = μ a (μ b c)

theorem op_assoc [Semigroup G] (a b c : G) : μ (μ a b) c = μ a (μ b c) := Semigroup.op_assoc a b c

/- Next is a monoid, which has the properties of a semigroup, along with an identity. -/
class Monoid (G : Type*) extends Semigroup G where
  protected id : G
  protected op_id : ∀ a : G, μ a id = a
  protected id_op : ∀ a : G, μ id a = a

def 𝕖 [Monoid G] : G := Monoid.id

theorem op_id [Monoid M] (a : M) : μ a 𝕖 = a := Monoid.op_id a

theorem id_op [Monoid M] (a : M) : μ 𝕖 a = a := Monoid.id_op a

/- Commutative monoids have a new property, the commutative property. This means that a * b = b * a
for any a or b. -/
class CommMonoid (G : Type*) extends Monoid G where
  protected op_comm : ∀ a b : G, μ a b = μ b a

theorem op_comm [CommMonoid M] (a b : M) : μ a b = μ b a := CommMonoid.op_comm a b

/- Now, we can return to the definition of a group-/
class Group (G : Type*) extends Monoid G where
  protected inv : G → G
  protected inv_op : ∀ a : G, μ (inv a) a = 𝕖

def ι [Group G] : G → G := Group.inv

theorem inv_op [Group G] (a : G) : μ (ι a) a = 𝕖 := Group.inv_op a

/- The last structure is an Abelian group, which is a group with the commutative property. -/
class AbelianGroup (G : Type*) extends Group G, CommMonoid G

/- These are the definitions that will be used moving forwards. -/

/- Now, try to prove a theorem using the new definitions. -/
theorem left_cancel [Group G] (a b c : G) : μ a b = μ a c → b = c := by
  -- sorry
  -- SAMPLE SOLUTION
  intro h
  rw[←(id_op b), ←(id_op c), ←(inv_op a), op_assoc, op_assoc, h]
  -- END OF SAMPLE SOLUTION
