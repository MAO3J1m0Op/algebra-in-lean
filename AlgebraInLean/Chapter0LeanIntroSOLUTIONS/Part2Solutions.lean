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

Sheet 2
intro
exact
apply
trivial
exfalso (not in natural num)
nth_rewrite
-/

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

/-Section 1 Sheet 1-/
variable (P Q R S T : Prop)

example : P → P := by
  intro h
  exact h
  done

example : P → Q → P := by
  intro h1
  intro h2
  exact h1
  done

example : P → (P → Q) → Q := by
  intro h1 h2
  apply h2 at h1
  exact h1
  done

example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 h3
  apply h1 at h3
  apply h2 at h3
  exact h3
  done

example : (P → Q → R) → (P → Q) → P → R := by
  intro h1 h2 h3
  apply h1
  exact h3
  apply h2 at h3
  exact h3
  done

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro h1 h2 h3 h4 h5
  apply h2 at h5
  apply h4 at h5
  apply h3 at h5
  exact h5
  done

example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1 h2
  apply h1
  apply h2
  exact h1
  done

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1 h2 h3
  apply h2
  intro h4
  apply h1
  intro h5
  exact h4
  done

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  apply h1
  intro h4
  apply h3
  apply h2
  exact h4
  done

example : (((P → Q) → Q) → Q) → P → Q := by
  intro h1 h2
  apply h1
  intro h3
  apply h3
  exact h2
  done

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  intro h1 h2 h3
  apply h2
  intro h4 h5 h6
  apply h4
  intro h7
  exact h5
  done

/-Section 1 Sheet 2-/

example : True := by
  trivial
  done

example : True → True := by
  intro h1
  trivial
  done

example : False → True := by
  intro h1
  trivial
  done

example : False → False := by
  intro h1
  exact h1
  done

example : (True → False) → False := by
  intro h1
  apply h1
  trivial
  done

example : False → P := by
  intro h1
  exfalso
  exact h1
  done

example : True → False → True → False → True → False := by
  intro h1 h2 h3 h4 h5
  exact h2
  done

example : P → (P → False) → False := by
  intro h1 h2
  apply h2 at h1
  exact h1
  done

example : (P → False) → P → Q := by
  intro h1 h2
  apply h1 at h2
  exfalso
  exact h2
  done

example : (True → False) → P := by
  intro h1
  exfalso
  apply h1
  trivial
  done

/-Section 1 Sheet 5-/

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw[h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rw[h2] at h1
  exact h1
  done
