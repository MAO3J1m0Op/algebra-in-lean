/-
This is a solutions sheet.
-/

import Mathlib.Tactic

/-
Welcome!

This is an interactive problem set, where you'll learn to use Lean 4,
a theorem prover and programming language, while exploring the basics
of abstract algebra. Through formalizing and proving theorems on groups,
rings, and fields, you'll become comfortable with using Lean 4 to
help you verify theorems in a user-friendly way.

This problem set is written under the assumption that you, the user, have
already completed the Natural Number Game: <https://adam.math.hhu.de/#/g/leanprover-community/nng4>
Additionally, it is assumed that the user is in the process of taking
(or is already familiar with) an abstract algebra class, so explanations
of concepts will be more concise than a textbook's.

There are solutions provided for your reference. Should you be interested in
learning more about specific tactics, Lean 4 documentation is available online.

Learn about all things Lean 4 here: <https://leanprover-community.github.io/index.html>
Full documentation can be found here: <https://leanprover-community.github.io/mathlib4_docs/>

****

Before we dive into abstract algebra in World 1, we will begin with the basics
of Lean in World 0. If you are already familiar with using Lean, feel free to
skip World 0 and dive straight into World 1.

As you saw in the Natural Number Game, in Lean, theorems are proven using the help
of tactics. World 0 will familiarize you with a few basic tactics through some
exercises concerning logic and basic arithmetic.

To get you used to reading Lean, let us begin with a very basic exercise from
the Natural Number Game.
--/

example : 37 * x + q = 37 * x + q := by
  rfl

/-
The above example is the very first level of the Natural Number Game.
In the Natural Number Game, you typed a tactic into a text box, and
the active goals updated. Here, it is a little different.

Putting your cursor after the word "by," you should see the Tactic State
appear in your Lean Infoview window to the right of your screen.
There, you will see what you saw in the Natural Number Game as "Objects" and
"Active Goals". What you see after the "⊢" is your Active Goal, and it will
update as you write tactics.

We complete exercises just as we did in the Natural Number Game.
This example can be completed by rfl, just as it was in the Natural Number Game.
Putting your cursor to the right of rfl, you will see in the Lean Infoview that
the Tactic State has updated to read "No goals." This is what we want to see
with all of our exercises by the time we're done going through this problem set!

Let's see another example from the Natural Number Game, but this time,
you try completing it yourself! The tactic "sorry" is used as a placeholder in Lean.
Deleting it will show the objects and goals. After you write a new tactic,
go to a new line. The tactic "done" is used to indicate that the exercise
or theorem is complete.

This example can be done entirely using the rw tactic and theorems
that you used in the Natural Number Game.
-/

example (a b c : Nat) : (a + b) + c = (a + c) + b := by
  rw [add_assoc]
  rw [add_assoc]
  rw [add_comm b]
  done

/-
Note that as you write each tactic line by line, the goal updates. You can
go back to see how the goal updated by simply placing your cursor at the right
end of any line.

****

Now that you've gotten used to reading Lean, let's go on to the next sheet!
-/
