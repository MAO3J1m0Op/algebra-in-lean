import AlgebraInLean.World01.Sheet3

namespace AlgebraInLean

/- Now that we know how to define a group, and some basic properties of groups, we can find
important examples of groups. -/

/- The group you are likely most familiar with is the integers, with addition as the group
operation. -/
instance : Group ℤ where
  -- fun x y => x + y means that op is a function where op x y is defined as x + y
  op := fun x y => x + y

  -- Mathlib already has proofs for all of these properties, try to use those.
  op_assoc := by
    -- sorry
    -- SAMPLE SOLUTION
    exact add_assoc
    -- END OF SAMPLE SOLUTION

  id :=
    -- sorry
    -- SAMPLE SOLUTION
    0
    -- END OF SAMPLE SOLUTION

  op_id := by
    -- sorry
    -- SAMPLE SOLUTION
    exact add_zero
    -- END OF SAMPLE SOLUTION

  id_op := by
    -- sorry
    -- SAMPLE SOLUTION
    exact zero_add
    -- END OF SAMPLE SOLUTION

  inv :=
    -- sorry
    -- SAMPLE SOLUTION
    fun a => -a
    -- END OF SAMPLE SOLUTION

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    exact add_left_neg
    -- END OF SAMPLE SOLUTION

/- Structures other than numbers also have the group properties. Take the rotational symmetries of a
polygon, for example. Each element could be a rotation that maintains the symmetries of the polygon,
and the group operation can be composition of these rotations. For example, consider the rotations
of a triangle. All symmetric rotations must be multiples of 120°, of which there are three:
{0°, 120°, 240°}. Any other rotations can be written as one of these three and some amount of
360° rotations. Now, we can prove that this set, commonly called C3, is a group.-/

/- The inductive keyword allows us to define a type with specific elements. In this case, we define
C3 to have 3 elements: rot0, rot120, and rot240. These three elements are the three rotational
symmetries of a triangle. -/
inductive C3 : Type
  | rot0 : C3
  | rot120 : C3
  | rot240 : C3

/- In order to define how we compose different rotations, we have to first define functions for each
of the three rotations, then define the group operation based on these functions. -/

-- Rotation by 0°
def fun_rot0 : C3 → C3
  | C3.rot0 => C3.rot0 -- This means rot0 maps to rot0 after a rotation of 0°
  | C3.rot120 => C3.rot120
  | C3.rot240 => C3.rot240

-- Rotation by 120°
def fun_rot120 : C3 → C3
  | C3.rot0 => C3.rot120
  | C3.rot120 => C3.rot240
  | C3.rot240 => C3.rot0

-- Rotation by 240°
def fun_rot240 : C3 → C3
  | C3.rot0 => C3.rot240
  | C3.rot120 => C3.rot0
  | C3.rot240 => C3.rot120

/- Now, we can define the group operation using these three functions. -/
def fC3 : C3 → C3 → C3
  | C3.rot0 => fun_rot0
  | C3.rot120 => fun_rot120
  | C3.rot240 => fun_rot240

/- We should also define the inverse function, which should "undo" rotation. -/
def fC3inv : C3 → C3
  | C3.rot0 =>
    -- sorry
    -- SAMPLE SOLUTION
    C3.rot0
    -- END OF SAMPLE SOLUTION
  | C3.rot120 =>
    -- sorry
    -- SAMPLE SOLUTION
    C3.rot240
    -- END OF SAMPLE SOLUTION
  | C3.rot240 =>
    -- sorry
    -- SAMPLE SOLUTION
    C3.rot120
    -- END OF SAMPLE SOLUTION

/- Now, we can prove that C3 is a group.
The cases tactic is very useful here, along with the all_goals tactic, which allows you to solve
multiple goals at the same time. Once you have an equation such as μ C3.rot120 C3.rot240 = C3.rot0,
the rfl tactic will solve the goal. -/
instance : Group C3 where
  op := fC3

  op_assoc := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a b c
    cases a
    all_goals cases b
    all_goals cases c
    all_goals rfl
    -- END OF SAMPLE SOLUTION

  id :=
    -- sorry
    -- SAMPLE SOLUTION
    C3.rot0
    -- END OF SAMPLE SOLUTION

  op_id := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    cases a
    all_goals rfl
    -- END OF SAMPLE SOLUTION

  id_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    cases a
    all_goals rfl
    -- END OF SAMPLE SOLUTION

  inv := fC3inv

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    cases a
    all_goals rfl
    -- END OF SAMPLE SOLUTION
