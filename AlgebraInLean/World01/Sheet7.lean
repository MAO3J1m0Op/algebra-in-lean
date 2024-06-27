import AlgebraInLean.World01.Sheet6
open Defs

def Sn (n : ℕ) : Type := {f : Fin n → Fin n | ∃ g : Fin n → Fin n, ∀ x : Fin n, f (g x) = x ∧ g (f x) = x}

--def Sn_op (n : ℕ) : Sn n → Sn n → Sn n := fun f g => fun x => f (g x)



instance (n : ℕ) (hpos : NeZero n) : Defs.Group (Sn n) where
  op := sorry

  op_assoc := by
    sorry

  id := sorry

  op_id := by
    sorry

  id_op := by
    sorry

  inv := sorry

  inv_op := by
    sorry
