/-
This is a solutions sheet.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
/-
The tactic `constructor` should be completely new to you. It is very useful for deconstructing
goals that use `∧` ("and"). It is similar to the `cases` tactic in the way that it breaks up one
goal into multiple goals to be completed, but it is used on the goal rather than on a hypothesis.
`constructor` is also helpful for some other structures like ↔ or ∃.

Let's take a look at the example below:
-/

variable (P Q R S T : Prop)

/-START EXAMPLE-/
/- FM Section 1 Sheet 4 -/
example : P → Q → P ∧ Q := by
  intro h1 h2
  constructor
  · exact h1
  · exact h2
  done
/-END EXAMPLE-/

/-
Note that `constructor` breaks up the goal `⊢ P ∧ Q` into `⊢ P` and `⊢ Q`.

With the `constructor` tactic comes the need to talk about some helpful formatting in Lean. The `·`
that you see above is used to indicate steps to solve separate goals.

- `⊢ P` is one goal, so a `·` is added. `exact h1` solves this first goal.
- `⊢ Q` is the next goal, so another `·` is added. `exact h2` solves this second goal.

In the case where more than one tactic is requred to solve the goal, lines following the line with
the new `·` are indented to indicate that they are associated with this specific goal.

For example:
-/

/-START EXAMPLE-/
/- FM Section 1 Sheet 5 -/
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro h1
    rw [h1]
  · intro h2
    rw [h2]
  done
/-END EXAMPLE-/

/-
Note that in the above example, `constructor` is used to break up an if and only if statement.

See if you can complete the following exercises. The last few are a bit tricky! Don't forget all of
the tactics you've learned so far, and try to use our newly learned formatting.
-/

/- FM Section 1 Sheet 4 -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  cases h1 with
  | intro left right =>
    constructor
    · exact right
    · exact left
  done

/- FM Section 1 Sheet 4 -/
example : P → P ∧ True := by
  intro h1
  constructor
  · exact h1
  · trivial
  done

/- FM Section 1 Sheet 4 -/
example : False → P ∧ False := by
  intro h1
  constructor
  · exfalso
    exact h1
  · exact h1
  done

/- FM Section 1 Sheet 4 -/
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

/- FM Section 1 Sheet 4 -/
example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  · exact h2
  · exact h3
  done

/- FM Section 1 Sheet 5 -/
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

/- FM Section 1 Sheet 6 -/
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

/- FM Section 1 Sheet 6 -/
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

/- On to the next part! -/
