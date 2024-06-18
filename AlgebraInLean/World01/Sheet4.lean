import AlgebraInLean.World01.Sheet3
open Defs

/- Now that we know how to define a group, and some basic properties of groups,
we can find important examples of groups-/

/- The group you are likely most familiar with is the integers, with addition
as the group operation.-/
instance : Defs.Group ℤ where
  op := fun x y => x + y

  op_assoc := by -- Mathlib already has a proof that the addition is associative, try to use that
    -- sorry
    -- SAMPLE SOLUTION
    intro a b c
    exact Int.add_assoc a b c
    -- END OF SAMPLE SOLUTION

  id :=
    -- sorry
    -- SAMPLE SOLUTION
    0
    -- END OF SAMPLE SOLUTION

  op_id := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    exact Int.add_zero a
    -- END OF SAMPLE SOLUTION

  id_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    exact Int.zero_add a
    -- END OF SAMPLE SOLUTION

  inv :=
    -- sorry
    -- SAMPLE SOLUTION
    fun a => -a
    -- END OF SAMPLE SOLUTION

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    exact Int.add_left_neg a
    -- END OF SAMPLE SOLUTION

/- Structures other than numbers also have the group properties. Take the
symmetries of rotating a polygon, for example. Each element could be a
rotation that maintains the symmetries of the polygon, and the group operation
can be composition of these rotations. For example, consider the rotations of
a triangle. All symmetric rotations must be multiples of 120°, of which there
are three: {0°, 120°, 240°}. Any other rotations can be written as one of
these three and some amount of 360° rotations. Now, we can prove that
this set, commonly called C3, is a group.-/

/- This defines the type C3, with three elements, rot0, rot120, and rot240-/
inductive C3 : Type
  | rot0 : C3
  | rot120 : C3
  | rot240 : C3

/- The three following definitions define how rotation by each angle affects
each angle. -/
def frot0 : C3 → C3 -- Rotation by 0°
  | C3.rot0 => C3.rot0 -- This means rot0 maps to rot0 after a rotation of 0°
  | C3.rot120 => C3.rot120
  | C3.rot240 => C3.rot240

def frot120 : C3 → C3 --
  | C3.rot0 => C3.rot120
  | C3.rot120 => C3.rot240
  | C3.rot240 => C3.rot0

def frot240 : C3 → C3
  | C3.rot0 => C3.rot240
  | C3.rot120 => C3.rot0
  | C3.rot240 => C3.rot120

/- Now, we can define the group operation using these three functions-/
def fC3 : C3 → C3 → C3
  | C3.rot0 => frot0
  | C3.rot120 => frot120
  | C3.rot240 => frot240

/- It will be helpful to define the inverse function first-/
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
The cases tactic is very useful here, along with the all_goals tactic, which allows
you to solve multiple goals at the same time-/
instance : Defs.Group C3 where
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
