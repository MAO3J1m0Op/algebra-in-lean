/-
This is a solutions sheet.
-/

import Mathlib.Tactic

/-
The `linter.unusedTactic` command permits the usage of the `done` tactic without warnings. You will
see this in every sheet.

FIXME: Find a more optimal solution for disabling this linter globally.
-/
set_option linter.unusedTactic false
/-
The `linter.unusedVariables` command ignores unused variables warnings in select sheets.
-/

set_option linter.unusedVariables false
/-this allows us to define variables that go on to be unused in an exercise-/

/-
Some exercises in this chapter are adapted from Kevin Buzzard's Natural Number Game, as well as his
course Formalising Mathematics. If you would like to learn more about Lean, Buzzard's Formalising
Mathematics course goes more in depth in relation to numerous undergraduate math topics. Exercises
adapted from Buzzard's work will be marked as such.

Formalising Mathematics can be found here:
<https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/index.html>
-/

/-
Many basic tactics in Lean are best introduced through logic exercises. You already know `rfl` and
`rw` from the Natural Number Game (NNG), and you are also already familiar with a few other basic
tactics. However, keep in mind that the way these tactics work in the Natural Number Game may be
slightly different than the way that they are actually used in Lean. These differences mostly boil
down to slight discrepancies in syntax.

Mathlib is a library of mathematical structures and theorems formalized in Lean. Theorems in Mathlib
are named and can be used in other proofs. An overview of the topics currently in Mathlib can be
found here: <https://leanprover-community.github.io/mathlib-overview.html> Note that `#check` tells
the type. For propositions, this will tell you the definition of a proposition in Mathlib. For
example:
-/

#check zero_add

/-
Let's start with a few tactics that you are already familiar with from the NNG:

- exact
- apply
- intro

To continue getting used to reading Lean and working with the Lean Infoview, let's do a few levels
from the NNG. Don't forget that you can also use `rw` and `rfl`! Delete the `sorry`s and fill in the
proofs.
-/

/- NNG Implication World Level 1 -/
example (x y z : Nat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1
  done

/-
NNG Implication World Level 2
hint: zero_add still works outside of the NNG, as it is a theorem proven in Mathlib.
-/
example (y x : Nat) (h1 : 0 + x = 0 + y + 2) : x = y + 2 := by
  rw [zero_add] at h1
  rw [zero_add] at h1
  exact h1
  done

/- NNG Implication World Level 3 -/
example (x y : Nat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1
  done

/- NNG Implication World Level 6 -/
example (x : Nat) : x = 37 → x = 37 := by
  intro h1
  exact h1
  done

/-
Let's move on beyond the NNG to do some exercises you haven't seen before. The following exercises
are from Kevin Buzzard's Formalizing Mathematics.
-/

variable (P Q R S T : Prop)
/-
This variable declaration indicates that for the rest of the file, references to P, Q, R, S
and T will all be references to arbitrary values of type Prop.
-/

/- FM Section 1 Sheet 1 -/
example : P → P := by
  intro h
  exact h
  done

/- FM Section 1 Sheet 1 -/
/-
Note going forward that the function arrow → is right-associative, so P → Q → P is the same thing
as P → (Q → P).
-/
example : P → Q → P := by
  intro h1
  intro h2
  exact h1
  done

/- FM Section 1 Sheet 1 -/
example : P → (P → Q) → Q := by
  intro h1 h2
  apply h2 at h1
  exact h1
  done

/- FM Section 1 Sheet 1 -/
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 h3
  apply h1 at h3
  apply h2 at h3
  exact h3
  done

/- FM Section 1 Sheet 1 -/
example : (P → Q → R) → (P → Q) → P → R := by
  intro h1 h2 h3
  apply h1
  exact h3
  apply h2 at h3
  exact h3
  done

/- FM Section 1 Sheet 1 -/
example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro h1 h2 h3 h4 h5
  apply h2 at h5
  apply h4 at h5
  apply h3 at h5
  exact h5
  done

/- FM Section 1 Sheet 1 -/
example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1 h2
  apply h1
  apply h2
  exact h1
  done

/- FM Section 1 Sheet 1 -/
example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1 h2 h3
  apply h2
  intro h4
  apply h1
  intro h5
  exact h4
  done

/- FM Section 1 Sheet 1 -/
example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  apply h1
  intro h4
  apply h3
  apply h2
  exact h4
  done

/- FM Section 1 Sheet 1 -/
example : (((P → Q) → Q) → Q) → P → Q := by
  intro h1 h2
  apply h1
  intro h3
  apply h3
  exact h2
  done

/- FM Section 1 Sheet 1 -/
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

/-
The `↔` means "if and only if". If you are ever curious how to type a certain Lean symbol in VSCode,
just hover over it for a few seconds in VSCode. `rw` can also be applied with `↔` hypotheses.
-/

/- FM Section 1 Sheet 5 -/
example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

/- FM Section 1 Sheet 5 -/
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rw [h2] at h1
  exact h1
  done

/-
Note that many of the exercises above could be solved in one line, using the tactic `tauto`, just
as some levels in NNG could be solved by `tauto`.
-/

/-
Lean also has the propositions `True` and `False`, which correspond to propositions that are
definitionally true or false, respectively.

If the goal is `True`, it can be solved with the tactic `trivial`.

For example:
-/

/-START EXAMPLE-/
/- FM Section 1 Sheet 2 -/
example : True := by
  trivial
  done
/-END EXAMPLE-/

/- Let's do some exercises, adding `trivial` to our list of tactics. -/

/- FM Section 1 Sheet 2 -/
example : True → True := by
  intro h1
  trivial
  done

/- FM Section 1 Sheet 2 -/
example : False → True := by
  intro h1
  trivial
  done

/- FM Section 1 Sheet 2 -/
example : False → False := by
  intro h1
  exact h1
  done

/- FM Section 1 Sheet 2 -/
example : (True → False) → False := by
  intro h1
  apply h1
  trivial
  done

/- FM Section 1 Sheet 2 -/
example : True → False → True → False → True → False := by
  intro h1 h2 h3 h4 h5
  exact h2
  done

/- FM Section 1 Sheet 2 -/
example : P → (P → False) → False := by
  intro h1 h2
  apply h2 at h1
  exact h1
  done

/-
The tactic `exfalso` changes the goal (the part after the `⊢` symbol) to `False`. This is valid by
the principle of explosion (called "ex falso, sequitur quodlibet" in Latin, meaning "from false,
everything follows").

For example:
-/

/-START EXAMPLE-/
/- FM Section 1 Sheet 2 -/
example : False → P := by
  intro h1
  exfalso
  exact h1
  done
/-END EXAMPLE-/

/- Let's do some exercises. -/

/- FM Section 1 Sheet 2 -/
example : (P → False) → P → Q := by
  intro h1 h2
  apply h1 at h2
  exfalso
  exact h2
  done

/- FM Section 1 Sheet 2 -/
example : (True → False) → P := by
  intro h1
  exfalso
  apply h1
  trivial
  done

/-
To wrap up this part, note that the more advanced form of the `rw` tactic is `nth_rw` (which behaves
similarly to `nth_rewrite`). This example from the NNG shows it in use:
-/

/-START EXAMPLE-/
/- NNG Advanced Addition World Level 3 -/
example (x y : Nat) : x + y = y → x = 0 := by
  intro h1
  nth_rw 2 [←zero_add y] at h1
  apply add_right_cancel at h1
  exact h1
  done
/-END EXAMPLE-/

/-
Note that tactics `exact` and `apply` both have variants, `exact?` and `apply?`, which both go into
Mathlib's theorems/lemmas to search for something applicable to the proof. `exact?` looks for
theorems that close the goal, while `apply?` looks for theorems that can be used with the tactic
`apply` to the goal. `exact?` and `apply?` do not always work, as there are not always helpful
lemmas.

On to the next part!
-/
