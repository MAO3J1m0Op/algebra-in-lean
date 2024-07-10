import Mathlib.Tactic

namespace AlgebraInLean

namespace GroupIntro

/-
Abstract algebra is the branch of mathematics concerning sets and operations on those sets. For
example, consider the set of integers and the operation of addition on them. This operation has
certain properties, such as associativity and commutativity. The integers are one of many different
structures that algebra studies. Function composition, symmetries of regular polygons, and many
other ideas can all be understood through algebra.
-/

/--
The most common structure in algebra is the group. A group is defined as a set G along with some
binary operation on that set that satisfies some properties (listed below). This is represented in
Lean as a type class, which are objects that share certain properties. For a given type `G`, the
type `Group G` corresponds to it being a group; as an argument, this is often written `[Group G]`,
which makes Lean automatically look for an implementation of such.
-/
class Group (G : Type*) where
  /-
  The syntax `Type*` is explained further in chapter 2, but for now you can interpret it as just
  meaning that `G` can be really any type. More information here:
  <https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html>
  -/

  /--
  The group operation as a binary function. This type signature implies that it is necessarily
  closed.
  -/
  op : G → G → G

  /-- (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c) -/
  op_assoc : ∀ (a b c : G), op (op a b) c = op a (op b c)

  /-- The identity element of the group (denoted "e"), with properties described below -/
  id : G

  /-- a ⬝ e = a -/
  op_id : ∀ (a : G), op a id = a

  /-- e ⬝ a = a -/
  id_op : ∀ (a : G), op id a = a

  /-- For `x : G`, `inv x` is its inverse, with the property described below -/
  inv : G → G

  /-- a⁻¹ ⬝ a = e -/
  inv_op : ∀ (a : G), op (inv a) a = id

  /-
  This is another property of the inverse, but it can be shown from the other properties without
  additional assumptions, as shown below.
  -/
  -- op_inv : ∀ (a : G), μ a (inv a) = id

/-
Now that groups have been defined, you can state the group axioms as theorems and definitions to
make them easier to use.
-/

variable {G : Type*} [Group G] -- This allows us to omit these arguments from type signatures

/-- The group operation -/
def μ : G → G → G := Group.op -- hover over the `μ` (in VSCode) to see how to type it

/-- (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c) -/
theorem op_assoc : ∀ (a b c : G), μ (μ a b) c = μ a (μ b c) := Group.op_assoc

/-- The identity element of the group -/
def 𝕖 : G := Group.id

/-- a ⬝ e = a -/
theorem op_id : ∀ (a : G), μ a 𝕖 = a := Group.op_id

/-- e ⬝ a = a -/
theorem id_op : ∀ (a : G), μ 𝕖 a = a := Group.id_op

/-- The inverse map of the gorup -/
def ι [Group G] : G → G := Group.inv

/-- a⁻¹ ⬝ a = e -/
theorem inv_op [Group G] (a : G) : μ (ι a) a = 𝕖 := Group.inv_op a

/-
Now, we can start writing proofs with groups. Walk through this example, making sure you understand
every step.
-/

/-- a ⬝ a⁻¹ = e -/
theorem op_inv [Group G] (a : G) : μ a (ι a) = 𝕖 := by
  rw [←id_op (μ a _)]
  rw [←inv_op (ι a)]
  rw [op_assoc]
  rw [←op_assoc (ι a)]
  rw [inv_op]
  rw [id_op]
