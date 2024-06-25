/-
This is a solutions doc.
-/

import Mathlib.Tactic

/-EDIT THIS: Credit for exercises goes to Kevin Buzzard and his Formalizing Mathematics course.
If you would like to do some more practice and learn more about Lean, his course is
a great place to start!

OR exercises are from Natural Number Game.-/

/-
Many basic tactics in Lean are best introduced through logic exercises.
You already know rfl and rw from the Natural Number Game, and you are also
already familiar with a few other basic tactics. However, keep in mind that the
way these tactics work in the Natural Number Game may be slightly different than
the way that they are actually used in Lean. These differences mostly boil down
to slight discrepancies in syntax.

PLANNING

easy tactics in order of kevin buzzard
intro
exact
apply
triv
exfalso (not in natural num) (maybe end sheet here)
cases and induction
constructor (not in natural num)
rw
left and right
use
simp
symm

need to find something for
have
nth_rw (not in natural num)
split (maybe) (not in natural num)
specialize (maybe) (not in natural num)
mention assumption
mention formatting

-/

/-Current work in progress: converting levels from Natural Number Game
to use as exercises.-/

/-Implication World Level 1-/
example (x y z : Nat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1
  done

/-Implication World Level 2-/
example (y x : Nat) (h1 : 0 + x = 0 + y + 2) : x = y + 2 := by
  rw[zero_add] at h1
  rw[zero_add] at h1
  exact h1
  done

/-Implication World Level 3-/
example (x y : Nat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1
  done

/-Implication World Level 6-/
example (x : Nat) : x = 37 → x = 37 := by
  intro h1
  exact h1
  done

/-Advanced Addition World Level 3-/
example (x y : Nat) : x + y = y → x = 0 := by
  intro h1
  nth_rewrite 2 [← zero_add y] at h1
  apply add_right_cancel at h1
  exact h1
  done

/-Advanced Addition World Level 5-/
example (a b : Nat) : a + b = 0 → a = 0 := by
  sorry

/-Inequality World Level 1-/
example (x : Nat) : x ≤ x := by
  simp

/-Inequality World Level 2-/
example (x : Nat) : 0 ≤ x := by
  simp

/-Inequality World Level 4-/
example (x y z : Nat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry

/-Inequality World Level 7-/
example (x y : Nat) (h1 : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  sorry
