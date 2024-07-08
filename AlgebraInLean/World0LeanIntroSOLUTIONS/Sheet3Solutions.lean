/-
This is a solutions sheet.
-/

import Mathlib.Tactic

/-Credit for some exercises goes to Kevin Buzzard and his Formalizing Mathematics course OR to the
Natural Number Game. If you would like to learn more about Lean, Buzzard's course goes more in depth
in relation to numerous undergraduate math topics. When exercises are from either of these sources,
they will be clearly marked so as to give credit.

Formalising Mathematics can be found here:
<https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/index.html>-/

/-In the Natural Number Game, you used the tactics:

left
right

Let's do a couple warm up exercises from Formalizing Mathematics using these. Note that the ∨ symbol
means "or," just as it did in NNG.-/

variable (P Q R S T : Prop)

/-FM Section 1 Sheet 6-/
example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

/-FM Section 1 Sheet 6-/
example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

/-Also in the Natural Number Game, you learned a tactic called "cases". However, the functionality
and syntax you learned is actually closer to the tactic cases' (called cases prime), which is a more
specific functionality of the broader tactic. Let's now go over how to use the "cases" tactic.

First, let's look at an example:-/

/-FM Section 1 Sheet 4-/
example : P ∧ Q → P := by
  intro h1
  cases h1 with
  | intro left right =>
    exact left
  done

/-Note that the structure of the tactic looks a bit different. A shortcut to getting this structure
automatically generated rather than having to type it all out is to just type “cases h1” (or "cases
h1 with") and then perform the code action “Generate an explicit pattern match” when available (in
VSCode, this shows up as a yellow lightbulb to the left).

See if you can fill in the blank structure below:-/

/-FM Section 1 Sheet 4-/
example : P ∧ Q → Q := by
  intro h1
  cases h1 with
  | intro left right =>
    exact right
  done

/-Complete the exercises below. Note that the structure generated for cases is not always the
same.-/

/-NNG Inequality World Level 7-/
example (x y : Nat) (h1 : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h1 with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
  done

/-FM Section 1 Sheet 4-/
example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases h2 with
  | intro left right =>
    apply h1
    exact left
    exact right
  done

/-FM Section 1 Sheet 6-/
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

/-FM Section 1 Sheet 6-/
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

/-FM Section 1 Sheet 6-/
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

/-FM Section 1 Sheet 6-/
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

/-On to the next part!-/
