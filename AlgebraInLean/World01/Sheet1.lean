import Mathlib.Tactic

namespace AlgebraInLean

namespace GroupIntro

/- Abstract algebra is the branch of mathematics concerning sets and operations on those sets. For
example, consider the set of integers and the operation of addition on them. This operation has
certain properties, such as associativity and commutativity. The integers are one of many different
structures that algebra studies. Function composition, symmetries of regular polygons, and many
other ideas can all be understood through algebra. -/

/-- The most common structure in algebra is the group. A group is defined as a set G along with some
operation μ on that set. The operation also must have certain properties when acting on elements in
the set. This is represented in lean as a type class. Type classes are just objects that share
certain properties. The group class has the properties listed below, and a group G is
written as [Group G]. -/
class Group (G : Type*) where /- Type* means that G can be a type, a type consisting of types, or
  any nested amount of types within types. This is explained further in chapter 2, or you can look
  here: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html-/

  -- This is the function acting on the group, which must be closed
  μ : G → G → G

  -- The group operation must be associative
  op_assoc : ∀ a b c : G, μ (μ a b) c = μ a (μ b c)

  -- The group must have an identity element with properties described below
  id : G

  -- Multiplying any element by the identity returns the element
  op_id : ∀ a : G, μ a id = a

  -- Multiplying the identity by any element returns the element
  id_op : ∀ a : G, μ id a = a

  -- Each element must also have an inverse, which is represented by an inverse function
  inv : G → G

  -- Multiplying by an inverse returns the identity
  inv_op : ∀ a : G, μ (inv a) a = id

  -- This is another property of groups, but can be shown without extra assumptions
  -- op_inv : ∀ a : G, μ a (inv a) = id

/- Now that groups have been defined, you can state the group axioms as theorems and definitions to
make them easier to use-/

-- We still represent the group function as μ (written as \m)
def μ [Group G] : G → G → G := Group.μ

theorem op_assoc [Group G] (a b c : G) : μ (μ a b) c = μ a (μ b c) := Group.op_assoc a b c

-- We represent the identity as 𝕖 (written as \bbe)
def 𝕖 [Group G] : G := Group.id

theorem op_id [Group G] (a : G) : μ a 𝕖 = a := Group.op_id a

theorem id_op [Group G] (a : G) : μ 𝕖 a = a := Group.id_op a

-- We represent the inverse function as ι (written as \io)
def ι [Group G] : G → G := Group.inv

theorem inv_op [Group G] (a : G) : μ (ι a) a = 𝕖 := Group.inv_op a

/- Now, we can start writing proofs with groups-/

-- This is a proof that multiplying by the inverse gives the identity
theorem op_inv [Group G] (a : G) : μ a (ι a) = 𝕖 := by
  rw [(id_op (μ a (ι a))).symm, ←(inv_op (ι a))]
  rw [op_assoc, ←(op_assoc (ι a) a (ι a)), inv_op, id_op]
