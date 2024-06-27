/-
This is a solutions doc.
-/

import Mathlib.Tactic

/-Sheet 3
cases and induction
have
mention assumption?
mention specialize?
left and right-/

/-EDIT THIS: Credit for exercises goes to Kevin Buzzard and his Formalizing Mathematics course.
If you would like to do some more practice and learn more about Lean, his course is
a great place to start!

OR Exercises are from Natural Number Game.-/

/-Inequality World Level 7-/
example (x y : Nat) (h1 : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h1 with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
  done

variable (P Q R S T : Prop)
