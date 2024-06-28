/-
This is a solutions doc.
-/

import Mathlib.Tactic

/-Sheet 3
cases
have
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

/-Section 1 Sheet 4-/

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
  cases h1 with
  | inl h =>
    apply h2 at h
    exact h
  | inr h =>
    apply h3 at h
    exact h
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases h1 with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
  done

  example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  cases h3 with
  | inl h4 =>
    apply h1 at h4
    left
    exact h4
  | inr h4 =>
    apply h2 at h4
    right
    exact h4
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  cases h2 with
  | inl h3 =>
    apply h1 at h3
    left
    exact h3
  | inr h3 =>
    right
    exact h3
  done

/-
Still need exercises for
have
-/
