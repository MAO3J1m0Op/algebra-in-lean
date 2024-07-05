/-
This is a solutions sheet.
-/

import Mathlib.Tactic

/-Credit for some exercises goes to Kevin Buzzard and his Formalizing Mathematics
course OR to the Natural Number Game. If you would like to learn more about Lean,
Buzzard's course goes more in depth in relation to numerous undergraduate math topics.
When exercises are from either of these sources, they will be clearly marked so as
to give credit.

Formalising Mathematics can be found here:
<https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/index.html>-/

/-Let's wrap up our intro to Lean with some more straightforward tactics.
We will quickly go over:

simp
use
symm
induction
have

You have should have seen all of these previously in the Natural Number Game.

Let's begin with "simp". "Simp" uses lemmas already in mathlib as well as existing
hypotheses to simplify the goal. "Simp" has a wide range of uses, so if you are curious
about uses beyond the very simple examples shown below, looking up the documentation
is recommened.

Let's look at a couple examples:-/

/-NNG Inequality World Level 1-/
example (x : Nat) : x ≤ x := by
  simp
  done

example (x y : Nat) (h1 : x = 13) (h2 : y = 2) : x + y = 15 := by
  simp [h2]
  exact h1
  done

/-Now, see if you can complete the following exercises.-/

/-NNG Inequality World Level 2-/
example (x : Nat) : 0 ≤ x := by
  simp
  done

example (x : Nat) : x = x := by
  simp
  done

example (x y : Nat) (h1 : x = 13) (h2 : y = 2) : x + y = 15 := by
  simp [h1, h2]
  done

/-Moving on to the "use" tactic. A quick shortcut that indicates whether this tactic
will be handy is if "∃" appears. "Use" will replace that variable with whatever you
have input.

For example:-/

example : ∃ x : Nat, x + 3 = 34 := by
  use 31
  done

/-Complete the exercises below. "Simp" could also come in handy here.-/

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

/-The "symm" tactic is used to change a goal such as a ∼ b to b ∼ a. It works
only when the relation is symmetric or has previously been proven to be symmetric.

For example:-/

example (x y : Nat) (h1 : x = y) : y = x := by
  symm
  exact h1
  done

/-Here's a quick exercise for you:-/

example (x y z : Nat) (h1 : x = y * z) (h2 : z = 4) : y * 4 = x := by
  rw [h2] at h1
  symm
  exact h1
  done

/-The "induction" tactic is similar to the "cases" tactic in that it uses a specific
structure, and VSCode can automatically generate the structure once you type something
like "induction x with." Note that this is different from how you used induction
in the Natural Number Game, just as the cases tactic is different.

Try out these exercises using induction:-/

/-NNG Advanced Addition World Level 4-/
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

/-NNG Advanced Addition World Level 5-/
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

/-The "have" tactic should also be familiar to you. With the "have" tactic, the user
can add a new hypothesis to the list of existing hypotheses after proving it is true.

For example:-/

example (a : Nat) : a + 0 = a := by
  have h1 := add_zero a
  exact h1
  done

/-Here's a short exercise to wrap up.-/

example (a b c : Nat) (h1 : a = 32) (h2 : b = 4) (h3 : a + (b + c) = 60): 36 + c = 60 := by
  have h4 := add_assoc a b c
  rw [← h4] at h3
  simp [h1, h2] at h3
  exact h3
  done

/-Note that there could be many solutions to any given exercise.

Tactics like "assumption" and "specialize" are also helpful for dealing with multiple
hypotheses.

You now know enough tactics to progress beyond these simpler exercises to applying
what you know about Lean to abstract algebra. In future worlds, we go beyond only
working with the natural numbers or simple Prop variables to creating Groups as
defined in abstract algebra, so keep an eye out for the way these are made, as Types
are an important concept when working with Lean.

The final sheet in World 0 is a list of tactics mentioned so far and is for your
use as you see fit.

On to the next world!-/
