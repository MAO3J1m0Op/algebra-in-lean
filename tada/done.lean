import Lean.Elab.Tactic.Basic

open Lean Elab Tactic

@[inline]
elab "done" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfoAt (by assumption) f!"YASS ✨ PURR 😻 QUEEN 👑 SLAY 💅🏼"
  else
    logErrorAt (by assumption) f!"womp womp 💀"

example : 1 = 1 := by
  rfl
  done
