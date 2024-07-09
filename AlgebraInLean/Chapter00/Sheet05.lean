/-
This is a solutions sheet.
-/

import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
/-
Let's wrap up our intro to Lean with some more straightforward tactics. We will quickly go over:

- simp
- use
- symm
- induction
- have

You have should have seen all of these previously in the Natural Number Game.

Let's begin with `simp`. This tactic uses some previously-defined lemmas in Mathlib, as well as
existing hypotheses to simplify the goal. `simp` has a wide range of uses, so if you are curious
about uses beyond the very simple examples shown below, looking up the documentation is recommended.
For example, just as `exact` and `apply` have `exact?` and `apply?`, `simp` has `simp?`.

Let's look at a couple examples:
-/

/-START EXAMPLES-/
/- NNG Inequality World Level 1 -/
example (x : Nat) : x ≤ x := by
  simp
  done

example (x y : Nat) (h1 : x = 13) (h2 : y = 2) : x + y = 15 := by
  simp [h2]
  exact h1
  done
/-END EXAMPLES-/

/- Now, see if you can complete the following exercises. -/

/- NNG Inequality World Level 2 -/
example (x : Nat) : 0 ≤ x := by
  simp
  done

example (x : Nat) : x = x := by
  simp
  done

example (x y : Nat) (h1 : x = 13) (h2 : y = 2) : x + y = 15 := by
  simp [h1, h2]
  done

/-
Moving on to the `use` tactic. A quick shortcut that indicates whether this tactic will be handy is
if `∃ x` appears. `use x` will have you prove that `x` satisfies the condition in the `∃`.

For example:
-/

/-START EXAMPLE-/
example : ∃ (x : Nat), x + 3 = 34 := by
  use 31
  done
/-END EXAMPLE-/

/- Complete the exercises below. `simp` could also come in handy here. -/

example : ∃ (x y : Nat), 5 * x + 3 * y = 13 := by
  use 2
  use 1
  done

example : ∃ (x y z : Nat), 4 * y + 30 / z - 21 * x = 5 := by
  use 1, 5, 5
  done

example (y : ℤ) : ∃ (x z : ℤ), x * z = y := by
  use y
  use 1
  simp
  done

/-
The `symm` tactic is used to change a goal such as `a ∼ b` to `b ∼ a`. It works only when the
relation `~` is symmetric or has previously been proven to be symmetric, such as with equality.

For example:
-/

/-START EXAMPLE-/
example (x y : Nat) (h1 : x = y) : y = x := by
  symm
  exact h1
  done
/-END EXAMPLE-/

/- Here's a quick exercise for you: -/

example (x y z : Nat) (h1 : x = y * z) (h2 : z = 4) : y * 4 = x := by
  rw [h2] at h1
  symm
  exact h1
  done

/-
The `induction` tactic is similar to the `cases` tactic in that it uses a similar syntax, and VSCode
can automatically generate this once you type something like `induction x`. Note that this is
different from how you used `induction` in the Natural Number Game, just as the `cases` tactic is
different.

Try out these exercises using `induction`:
-/

/- NNG Advanced Addition World Level 4 -/
example (x y : Nat) : x + y = x → y = 0 := by
  induction x with
  | zero =>
    intro h1
    rw [zero_add] at h1
    exact h1
  | succ n ih =>
    intro h2
    simp at h2
    exact h2
  done

/- NNG Advanced Addition World Level 5 -/
example (a b : Nat) : a + b = 0 → a = 0 := by
  induction a with
  | zero =>
    intro h1
    rfl
  | succ n ih =>
    intro h2
    simp [h2] at ih
    simp [ih] at h2
    done

/-
The `have` tactic should also be familiar to you. With the `have` tactic, the user can add a new
hypothesis to the list of existing hypotheses after proving it is true. Keep in mind that `have` is
a useful tactic when applying "forwards logic," which is probably what you picture when writing
natural language proofs on paper. However, Lean proofs more often employ "backwards logic," where
the goal is edited to match a hypothesis. Both approaches work in proofs here.

For example:
-/

/-START EXAMPLE-/
example (a : Nat) : a + 0 = a := by
  have h1 := add_zero a
  exact h1
  done
/-END EXAMPLE-/

/- Here's a short exercise to wrap up. -/

example (a b c : Nat) (h1 : a = 32) (h2 : b = 4) (h3 : a + (b + c) = 60) : 36 + c = 60 := by
  have h4 := add_assoc a b c
  rw [← h4] at h3
  simp [h1, h2] at h3
  exact h3
  done

/-
Note that there could be many solutions to any given exercise.

Tactics like `assumption` and `specialize` are also helpful for dealing with multiple hypotheses.

You now know enough tactics to progress beyond these simpler exercises to applying what you know
about Lean to abstract algebra. In future chapters, we go beyond only working with the natural
numbers or simple Prop variables to creating algebraic structures such as groups. This means that
the types you will be working with will become more intricate and complex.

The final sheet in Chapter 0 is a list of tactics mentioned so far and is for your use as you see
fit.

On to the next chapter!
-/
