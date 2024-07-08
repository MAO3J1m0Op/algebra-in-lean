import AlgebraInLean.World01.Sheet4
open Defs

/- To represent Cn, the group of rotational symmetries of an n-gon, we will
use a type already in mathlib called Fin. Fin n is just the type of all natural
numbers less than n. Elements are represented as a pair of a natural number,
and a proof that that number is less than n. -/

/- The value n will represent a rotation of (n / 360) degrees. -/

instance (n : ℕ) (hpos : NeZero n): Defs.Group (Fin n) where
  /- Fin.add adds two elements in Fin n and then takes the result mod n. Since n is
  equivalent to a 360 degree rotation, this means that if you get a rotation over
  360 degrees, it gets changed to a rotation under 360 degrees. -/
  op := Fin.add

  /- Fin already has all of these proven, you just need to figue out what they are called.-/
  op_assoc := by
    exact add_assoc

  id := 0

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

  inv := fun n => -n

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    exact neg_add_self
    -- END OF SAMPLE SOLUTION
