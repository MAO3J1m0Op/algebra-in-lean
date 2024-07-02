/-
This is a solutions sheet.
-/

import Mathlib.Tactic

/-
Welcome!

This is an interactive problem set, where you'll learn to use Lean 4,
a theorem prover and programming language, while exploring the basics
of abstract algebra. Through exercises on groups, rings, and fields, you'll
formalize and verify mathematical proofs. By the end, you should be comfortable
with using Lean 4 to prove and verify theorems.

This problem set is written under the assumption that you, the user, have
already completed the Natural Number Game. Additionally, it is assumed that
the user is in the process of taking an abstract algebra class (i.e. 401 or 501),
so explanations of concepts will be more concise than a textbook's.

There are solutions provided for your reference. Should you be interested in
learning more about specific tactics, Lean 4 documentation is available online.

****

Before we dive into abstract algebra in Section 1, we will begin with the basics
of Lean in Section 0. As you saw in the Natural Number Game, in Lean, exercises
are completed using tactics. Section 0 will familiarize you with a few basic tactics
through some exercises concerning logic, functions, and sets.

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
There, you will see what you saw in the Natural Number Game as Objects and
Active Goals. What you see after the "⊢" is your Active Goal, and it will
update as you write tactics.

We complete exercises just as we did in the Natural Number Game.
This example can be completed by rfl, just as it was in the Natural Number Game.
Putting your cursor to the right of rfl, you will see in the Lean Infoview that
the Tactic State has updated to read "No goals." This is what we want to see
with all of our exercises by the time we're done going through this problem set!

Let's see another example from the Natural Number Game, but this time,
you try completing it yourself! The word "sorry" is used as a placeholder in Lean.
Deleting it will show the objects and goals. After you write a new tactic,
go to a new line. The word "done" is used to indicate that the exercise is complete.

This example can be done entirely using the rw tactic and theorems
that you used in the Natural Number Game.
-/

example (a b c : Nat) : (a + b) + c = (a + c) + b := by
  rw[add_assoc]
  rw[add_assoc]
  rw[add_comm b]
  done

/-
Note that as you write each tactic line by line, the goal updates. You can
go back to see how the goal updated by simply placing your cursor at the right
end of any line.

****

Now that you've gotten used to reading Lean, let's go on to the next sheet!
-/
