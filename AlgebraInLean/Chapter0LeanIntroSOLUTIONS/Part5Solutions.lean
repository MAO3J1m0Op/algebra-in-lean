/-
This is a solutions doc.
-/

import Mathlib.Tactic

/-Sheet 5
use
simp
symm
wrap up-/

/-EDIT THIS: Credit for exercises goes to Kevin Buzzard and his Formalizing Mathematics course.
If you would like to do some more practice and learn more about Lean, his course is
a great place to start!

OR Exercises are from Natural Number Game.-/

/-Inequality World Level 1-/
example (x : Nat) : x ≤ x := by
  simp

/-Inequality World Level 2-/
example (x : Nat) : 0 ≤ x := by
  simp

variable (P Q R S T : Prop)
