/-
This is a solutions doc.
-/

import Mathlib.Tactic

/-Sheet 4
constructor (not in natural num)
talk about formatting (\·)-/

/-EDIT THIS: Credit for exercises goes to Kevin Buzzard and his Formalizing Mathematics course.
If you would like to do some more practice and learn more about Lean, his course is
a great place to start!

OR Exercises are from Natural Number Game.-/

variable (P Q R S T : Prop)

/-Section 1 Sheet 4-/

example : P → Q → P ∧ Q := by
  intro h1 h2
  constructor
  · exact h1
  · exact h2
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  cases h1 with
  | intro left right =>
    constructor
    · exact right
    · exact left
  done

example : P → P ∧ True := by
  intro h1
  constructor
  · exact h1
  · trivial
  done

example : False → P ∧ False := by
  intro h1
  constructor
  · exfalso
    exact h1
  · exact h1
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases h1 with
  | intro left1 right1 =>
    cases h2 with
    | intro left2 right2 =>
      constructor
      · exact left1
      · exact right2
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  · exact h2
  · exact h3
  done

/-Section 1 Sheet 5-/

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro h1
    rw[h1]
  · intro h2
    rw[h2]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h1
    cases h1 with
    | intro left right =>
      constructor
      exact right
      exact left
  · intro h2
    cases h2 with
    | intro left right =>
      constructor
      · exact right
      · exact left
  done

/-Section 1 Sheet 6-/

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h1
    cases h1 with
    | inl h2 =>
      cases h2 with
      | inl h3 =>
        left
        exact h3
      | inr h3 =>
        right
        left
        exact h3
    | inr h4 =>
      right
      right
      exact h4
  · intro h5
    cases h5 with
    | inl h6 =>
      left
      left
      exact h6
    | inr h6 =>
      cases h6 with
      | inl h7 =>
        left
        right
        exact h7
      | inr h7 =>
        right
        exact h7
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  · intro h3
    cases h3 with
    | inl h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          left
          apply h5 at h4
          exact h4
    | inr h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          right
          apply h7 at h4
          exact h4
  · intro h3
    cases h3 with
    | inl h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          left
          apply h6 at h4
          exact h4
    | inr h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          right
          apply h8 at h4
          exact h4
  done
