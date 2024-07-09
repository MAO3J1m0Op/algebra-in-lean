import AlgebraInLean.Chapter01.Sheet03

namespace AlgebraInLean

/-
Now that we know how to define a group, and some basic properties of groups, we can find important
examples of groups.
-/

/-
The group you are likely most familiar with is the integers, with addition as the group operation.
-/
instance : Group ℤ where
  op a b := a + b

  -- Mathlib already has all of these proven, you just need to figure out what they are called.
  op_assoc := by
    exact add_assoc

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

  inv x :=
    -- sorry
    -- SAMPLE SOLUTION
    -x
    -- END OF SAMPLE SOLUTION

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    exact add_left_neg
    -- END OF SAMPLE SOLUTION

/- Moreover, the group formed by the integers is abelian -/
instance : AbelianGroup ℤ where
  op_comm := by
    -- sorry
    -- SAMPLE SOLUTION
    exact add_comm
    -- END OF SAMPLE SOLUTION

/-
Structures other than numbers also have the group properties. Take the rotational symmetries of a
regular polygon, for example. Each element could be a rotation that maintains the symmetries of the
polygon, and the group operation can be composition of these rotations. For example, consider the
rotations of such a triangle. All symmetric rotations must be multiples of 120°, of which there are
three: 0°, 120°, and 240°. Any other rotations can be written as one of these three and some amount
of 360° rotations. Now, we can prove that this set, commonly called C₃, is a group.
-/

/-
The inductive keyword allows us to define a type with specific elements/constructors. In this case,
we define C₃ to have the 3 elements C₃.rot0, C₃.rot120, and C₃.rot240 (the `C₃` before the `.` can
sometimes be omitted.
-/
/-- The rotational symmetries of a regular triangle. -/
inductive C₃ : Type
| rot0 : C₃
| rot120 : C₃
| rot240 : C₃

protected def C₃.op : C₃ → C₃ → C₃
| .rot0, .rot0 => .rot0
| .rot0, .rot120 => .rot120
| .rot0, .rot240 => .rot240
| .rot120, .rot0 => .rot120
| .rot120, .rot120 => .rot240
| .rot120, .rot240 => .rot0
| .rot240, .rot0 => .rot240
| .rot240, .rot120 => .rot0
| .rot240, .rot240 => .rot120

protected def C₃.inv : C₃ → C₃
  | .rot0 =>
    -- sorry
    -- SAMPLE SOLUTION
    .rot0
    -- END OF SAMPLE SOLUTION
  | .rot120 =>
    -- sorry
    -- SAMPLE SOLUTION
    .rot240
    -- END OF SAMPLE SOLUTION
  | .rot240 =>
    -- sorry
    -- SAMPLE SOLUTION
    .rot120
    -- END OF SAMPLE SOLUTION

/-
Now, we can prove that C₃ is a group. The tactics `cases` and `all_goals` (which applies a tactic
to all current goals) are useful here. Note that you can omit the `with | ...` part from `cases`.
-/
instance : Group C₃ where
  op := .op

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
    .rot0
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

  inv := .inv

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    cases a
    all_goals rfl
    -- END OF SAMPLE SOLUTION

/- C₃ is also abelian, but we leave a proof of that for the next section -/
