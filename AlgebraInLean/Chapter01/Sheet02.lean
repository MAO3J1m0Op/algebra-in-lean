import AlgebraInLean.Chapter01.Sheet01

namespace AlgebraInLean

/-
Groups aren't the only important structures in algebra. By including or excluding certain properties
from our definition, we create different structures.
-/

/-- A magma is the simples algebraic structure, which only has a closed binary operation -/
class Magma (α : Type*) where
  /-
  `protected` means that this definition should always be referenced as `Magma.op` since `μ` (below)
  should be used instead
  -/
  protected op : α → α → α

variable {α : Type*}

/-- The operation on a `Magma` or derived structure -/
def μ [Magma α] : α → α → α := Magma.op

/-- A semigroup is a magma where the operation is associative -/
class Semigroup (α : Type*) extends Magma α where
  -- extends means that it inherits the properties of a `Magma`
  protected op_assoc : ∀ (a b c : α), μ (μ a b) c = μ a (μ b c)

/-- (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c) -/
theorem op_assoc [Semigroup α] (a b c : α) : μ (μ a b) c = μ a (μ b c) := Semigroup.op_assoc a b c

/-- A monoid is a semigroup with identity -/
class Monoid (α : Type*) extends Semigroup α where
  protected id : α
  protected op_id : ∀ (a : α), μ a id = a
  protected id_op : ∀ (a : α), μ id a = a

/-- The identity element of a monoid or derived structure -/
def 𝕖 [Monoid α] : α := Monoid.id

/-- a ⬝ 1 = a -/
theorem op_id [Monoid α] : ∀ (a : α), μ a 𝕖 = a := Monoid.op_id

/-- 1 ⬝ a = a -/
theorem id_op [Monoid α] : ∀ (a : α), μ 𝕖 a = a := Monoid.id_op

/-- Commutative monoids have the additional property that the operation is commutative -/
class CommMonoid (α : Type*) extends Monoid α where
  protected op_comm : ∀ (a b : α), μ a b = μ b a

/-- a ⬝ b = b ⬝ a -/
theorem op_comm [CommMonoid α] (a b : α) : μ a b = μ b a := CommMonoid.op_comm a b

/-- A group is a monoid with inverses -/
class Group (α : Type*) extends Monoid α where
  protected inv : α → α
  protected inv_op : ∀ (a : α), μ (inv a) a = 𝕖

-- The inverse map of a group or derived structure -/
def ι [Group α] : α → α := Group.inv

/-- a⁻¹ ⬝ a = 𝕖 -/
theorem inv_op [Group α] (a : α) : μ (ι a) a = 𝕖 := Group.inv_op a

/-- An abelian group is a group with commutativity -/
class AbelianGroup (G : Type*) extends Group G, CommMonoid G

-- Lean doesn't automatically make these after the first extended class
instance [AbelianGroup α] : CommMonoid α where
  op_comm := op_comm


/-
These are the definitions that will be used moving forwards. Since the previous proof of `op_inv`
used the other definition of `Group`, we need to reprove it.
-/
/-- a ⬝ a⁻¹ = 1 -/
theorem op_inv [Group α] (a : α) : μ a (ι a) = 𝕖 := by
  rw [ ←id_op (μ a _)
     , ←inv_op (ι a)
     , op_assoc
     , ←op_assoc (ι a)
     , inv_op
     , id_op
     ]

/- Try to prove a theorem using the new definitions. -/
/-- a ⬝ b = a ⬝ c ⇒ b = c -/
theorem left_cancel [Group α] (a b c : α) (h : μ a b = μ a c) : b = c := by
  -- sorry
  -- SAMPLE SOLUTION
  rw [←id_op b, ←id_op c, ←inv_op a, op_assoc, op_assoc, h]
  -- END OF SAMPLE SOLUTION
