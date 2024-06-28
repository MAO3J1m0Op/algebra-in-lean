/-
This is a solutions doc.
-/

import Mathlib.Tactic

/-Sheet 5
use
simp
symm
induction
mention assumption
mention specialize
wrap up-/

/-EDIT THIS: Credit for exercises goes to Kevin Buzzard and his Formalizing Mathematics course.
If you would like to do some more practice and learn more about Lean, his course is
a great place to start!

OR Exercises are from Natural Number Game.-/

/-Inequality World Level 1-/
example (x : Nat) : x ≤ x := by
  simp
  done

/-Inequality World Level 2-/
example (x : Nat) : 0 ≤ x := by
  simp
  done

example (x : Nat) : x = x := by
  simp
  done

example (x y : Nat) (h1 : x = 13) (h2 : y = 2) : x + y = 15 := by
  simp [h2]
  exact h1
  done

example (x y : Nat) (h1 : x = 13) (h2 : y = 2) : x + y = 15 := by
  simp [h1, h2]
  done

/- "The simp tactic uses lemmas and hypotheses to simplify the main
goal target or non-dependent hypotheses. It has many variants." -/

example : ∃ x : Nat, x + 3 = 34 := by
  use 31
  done

example : ∃ x y : Nat, 5 * x + 3 * y = 13 := by
  use 2
  use 1
  done

example : ∃ x y z : Nat, 4 * y + 30 / z - 21 * x = 5 := by
  use 1, 5, 5
  done

example : ∃ x z : ℤ, x * z = y := by
  use y
  use 1
  simp
  done

example (x y : Nat) (h1 : x = y) : y = x := by
  symm
  exact h1
  done

example (x y z : Nat) (h1 : x = y * z) (h2 : z = 4) : y * 4 = x := by
  rw[h2] at h1
  symm
  exact h1
  done

/-Advanced Addition World Level 4-/
example (x y : Nat) : x + y = x → y = 0 := by
  induction x with
  | zero =>
    intro h1
    rw[zero_add] at h1
    exact h1
  | succ n ih =>
    intro h2
    simp at h2
    exact h2
  done

/-Advanced Addition World Level 5-/
example (a b : Nat) : a + b = 0 → a = 0 := by
  induction a with
  | zero =>
    intro h1
    rfl
  | succ n ih =>
    intro h2
    simp [h2] at ih
    simp[ih] at h2
    done
