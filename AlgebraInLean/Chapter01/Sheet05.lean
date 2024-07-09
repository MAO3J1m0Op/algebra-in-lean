import AlgebraInLean.Chapter01.Sheet04

namespace AlgebraInLean

/-
To represent Cₙ, the group of rotational symmetries of a regular n-gon, we will use a type already
in Mathlib called `Fin`. `Fin n` is the type of all natural numbers less than n. Elements are
represented as a pair of a natural number and a proof that it is less than n. A value `k : Fin n`
represents a rotation by 2kπ/n radians. Like the integers, this group is also abelian.
-/
instance (n : ℕ) [NeZero n] : AbelianGroup (Fin n) where
  /-
  Fin.add adds the two underlying integers and then considers its remainder under division by n.
  Since n itself is equivalent to a full rotation, this means that going over a full rotation wraps
  around to being less than 360°, like in the C₃ case.
  -/
  op := Fin.add

  -- Mathlib already has all of these proven, you just need to figure out what they are called.
  op_assoc := add_assoc

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

  inv := Neg.neg

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    exact neg_add_self
    -- END OF SAMPLE SOLUTION

  op_comm := by
    -- sorry
    -- SAMPLE SOLUTION
    exact add_comm
    -- END OF SAMPLE SOLUTION
