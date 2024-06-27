import Mathlib.Tactic
namespace Sheet1

/- Algebra primarily concerns how different mathematical objects combine.
For example, understanding how different integers interact through addition
can be very insightful. However, the integers are not the only objects in
mathematics that can interact. Function composition, rotation and reflection
of regular polynomials, and many other ideas can be captured through algebra-/


/- The most common structure in algebra is the group. A group is defined as a
set G along with some operation μ on that set. The operation also must have
certain properties when acting on elements in the set This is represented in
lean as a type class. Type classes are just objects that share certain
properties. -/

class Group (G : Type*) where -- This defines a group based on a Type G
  μ : G → G → G -- This is the function acting on the group, which must be closed
  op_assoc : ∀ a b c : G, μ (μ a b) c = μ a (μ b c) -- The group operation must be associative
  id : G -- The group must have an identity element with properties described below
  op_id : ∀ a : G, μ a id = a -- Multiplying any element by the identity returns the element
  id_op : ∀ a : G, μ id a = a -- Multiplying the identity by any element returns the element
  inv : G → G -- Each element must also have an inverse, which is represented by an inverse function
  inv_op : ∀ a : G, μ (inv a) a = id -- Multiplying by an inverse returns the identity
  --op_inv : ∀ a : G, μ a (inv a) = id -- This is another property of groups, but can be shown without extra assumptions

/- Now that groups have been defined, you can state the group axioms as theorems
and definitions to make them easier to use-/

def μ [Group G] : G → G → G := Group.μ -- We still represent the group function as μ (written as \m)

theorem op_assoc [Group G] (a b c : G) : μ (μ a b) c = μ a (μ b c) := Group.op_assoc a b c

def 𝕖 [Group G] : G := Group.id -- We represent the identity as 𝕖 (written as \bbe)

theorem op_id [Group G] (a : G) : μ a 𝕖 = a := Group.op_id a

theorem id_op [Group G] (a : G) : μ 𝕖 a = a := Group.id_op a

def ι [Group G] : G → G := Group.inv -- We represent the inverse function as ι (written as \io)

theorem inv_op [Group G] (a : G) : μ (ι a) a = 𝕖 := Group.inv_op a

/- Now, we can start writing proofs with groups-/

/- The simplest proof you can write is exactly one of the group axioms-/
/- This can be done using exact, but sometimes you have to use a theorem that
you don't know the name of. Try using the exact? tactic, which will help
autocomplete the proof. This tactic will be very useful later, when working
with theorems similar to ones already proven.-/
theorem op_assoc_exact [Group G] (a b c : G) : μ (μ a b) c = μ a (μ b c) := by
  -- sorry
  -- SAMPLE SOLUTION
  exact op_assoc a b c
  -- END OF SAMPLE SOLUTION

-- This is a proof that multiplying by the inverse gives the identity
theorem op_inv [Group G] (a : G) : μ a (ι a) = 𝕖 := by
  rw[(id_op (μ a (ι a))).symm, (inv_op (ι a)).symm]
  rw[op_assoc, (op_assoc (ι a) a (ι a)).symm, inv_op, id_op]
