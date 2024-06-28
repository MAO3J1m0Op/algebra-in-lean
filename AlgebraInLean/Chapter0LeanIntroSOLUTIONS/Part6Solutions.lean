import Mathlib.Tactic

/- Sheet 6
list of tactics for the user to keep updating -/

/- Tactics!

rfl
rw
done
sorry
intro
exact
apply
trivial
exfalso
cases
have
assumption
specialize
left
right
constructor
nth_rewrite
use
simp
symm
induction
-/

/-IGNORE ALL THIS BELOW I'm just storing it here for organizational purposes

PLANNING

Sheet 1
rfl
rw
done
sorry

Sheet 2
intro
exact
apply
trivial
exfalso (not in natural num)
nth_rewrite

Sheet 3
cases
have
left and right

Sheet 4
constructor (not in natural num)
talk about formatting (\·)

Sheet 5
use
simp
symm
induction
mention assumption
mention specialize
wrap up
-/


/-Levels from Natural Number Game-/

/-Inequality World Level 4-/
example (x y z : Nat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  induction x with
  | zero =>
    simp
  | succ n ih =>
    sorry
