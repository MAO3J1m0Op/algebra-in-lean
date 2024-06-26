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
  induction b with
  | zero =>
    intro h1
    rw[add_zero] at h1
    exact h1
  | succ n ih =>
    rw[← add_assoc]
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
  cases h1 with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
  done

/- work in progress: copy/pasting select exercises from Kevin Buzzard's
Formalizing Mathematics to be borrowed with credit given or modified.-/

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

/-Section 1 Sheet 4
need to redo changing cases' to cases-/

example : P ∧ Q → P := by
  intro h1
  cases h1 with
  | intro left right =>
    exact left
  done

example : P ∧ Q → Q := by
  intro h1
  cases h1 with
  | intro left right =>
    exact right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases h2 with
  | intro left right =>
    apply h1
    exact left
    exact right
  done

example : P → Q → P ∧ Q := by
  intro h1 h2
  constructor
  exact h1
  exact h2
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  cases h1 with
  | intro left right =>
    constructor
    exact right
    exact left
  done

example : P → P ∧ True := by
  intro h1
  constructor
  exact h1
  trivial
  done

example : False → P ∧ False := by
  intro h1
  constructor
  exfalso
  exact h1
  exact h1
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases h1 with
  | intro left1 right1 =>
    cases h2 with
    | intro left2 right2 =>
      constructor
      exact left1
      exact right2
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  exact h2
  exact h3
  done

/-Section 1 Sheet 5-/
example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw[h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rw[h1]
  intro h2
  rw[h2]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rw[h2] at h1
  exact h1
  done

example : P ∧ Q ↔ Q ∧ P := by /-START HERE-/
  constructor
  intro h1
  constructor
  cases' h1 with h2 h3
  exact h3
  cases' h1 with h4 h5
  exact h4
  intro h6
  constructor
  cases' h6 with h7 h8
  exact h8
  cases' h6 with h9 h10
  exact h9
  done

/-Section 1 Sheet 6-/

example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  cases' h1 with h4 h5
  apply h2 at h4
  exact h4
  apply h3 at h5
  exact h5
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases' h with h1 h2
  right
  exact h1
  left
  exact
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h1
  cases' h1 with h2 h3
  cases' h2 with h4 h5
  left
  exact h4
  right
  left
  exact h5
  right
  right
  exact h3
  intro h1
  cases' h1 with h2 h3
  left
  constructor
  exact h2
  cases' h3 with h4 h5
  left
  right
  exact h4
  right
  exact h5
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  cases' h3 with h4 h5
  left
  apply h1 at h4
  exact h4
  right
  apply h2 at h5
  exact h5
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  cases' h2 with h3 h4
  left
  apply h1 at h3
  exact h3
  right
  exact h4
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  intro h3
  cases' h3 with h4 h5
  left
  cases' h1 with h6 h7
  apply h6 at h4
  exact h4
  right
  cases' h2 with h6 h7
  apply h6 at h5
  exact h5
  intro h3
  cases' h3 with h4 h5
  cases' h1 with h5 h6
  left
  apply h6 at h4
  exact h4
  right
  cases' h2 with h6 h7
  apply h7 at h5
  exact h5
  done

/-
still need to cover

use
symm
have
nth_rw (have 1 ex from natural num game)
split (maybe) (not in natural num)
specialize (maybe) (not in natural num)
mention assumption
mention formatting
-/
