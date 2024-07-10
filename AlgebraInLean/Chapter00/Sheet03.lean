/-
This is a solutions sheet.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
/-
In the Natural Number Game, you used the tactics:

- left
- right

Let's do a couple warm up exercises from Formalizing Mathematics using these. Note that the `∨`
symbol means "or", just as it did in the NNG.
-/

variable (P Q R S T : Prop)

/- FM Section 1 Sheet 6 -/
example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

/- FM Section 1 Sheet 6 -/
example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

/-
Also in the Natural Number Game, you learned a tactic called `cases`. However, the functionality
and syntax you learned is actually closer to the tactic `cases'`, which is present for compatibility
with Lean3. Let's now go over how to use the `cases` tactic in Lean4.

First, let's look at an example:
-/

/-START EXAMPLE-/
/- FM Section 1 Sheet 4 -/
example : P ∧ Q → P := by
  intro h1
  cases h1 with
  | intro left right =>
    exact left
  done
/-END EXAMPLE-/

/-
Note that the syntax of the tactic looks a bit different. A shortcut to getting this syntax
automatically generated rather than having to type it all out is to just type `cases h1` and then
perform the code action "Generate an explicit pattern match" when available (in VSCode, this shows
up as a yellow lightbulb to the left).

See if you can fill in the blank structure below:
-/

/- FM Section 1 Sheet 4 -/
example : P ∧ Q → Q := by
  intro h1
  cases h1 with
  | intro left right =>
    /-START EXAMPLE-/
    exact right
    /-END EXAMPLE-/
  done

/-
Complete the exercises below. Note that the exact syntax generated for `cases` is not always the
same.
-/

/- NNG Inequality World Level 7 -/
example (x y : Nat) (h1 : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h1 with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
  done

/- FM Section 1 Sheet 4 -/
example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases h2 with
  | intro left right =>
    apply h1
    exact left
    exact right
  done

/- FM Section 1 Sheet 6 -/
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

/- FM Section 1 Sheet 6 -/
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

/- FM Section 1 Sheet 6 -/
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

/- FM Section 1 Sheet 6 -/
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

/- On to the next part! -/
