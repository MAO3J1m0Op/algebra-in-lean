import AlgebraInLean.World01.Sheet4

namespace AlgebraInLean

/- To represent Cn, the group of rotational symmetries of an n-gon, we will
have a function mapping any natural number n to the set of all n rotational
symmetries of an n-gon. Fin n is just the type of all natural numbers less than n-/
def Cn (n : ℕ): Type := Fin n

/- Fin n already has an add function that automatically takes mod n. This is
equivalent to a rotation of more than 360° being converted to a rotation of
less than 360°-/
def fCn (n : ℕ) : (Cn n) → (Cn n) → (Cn n) := Fin.add

/- Again we define the inverse function before proving that Cn is a group-/
def fCn_inv (n : ℕ): (Fin n) → (Fin n) := fun x => -x


instance (n : ℕ) (hpos : NeZero n): Group (Cn n) where
  op := fCn n

  op_assoc := by
    intro a b c
    have h : ∀ (a b c : Fin n), a + b + c = a + (b + c)
    exact fun a b c => add_assoc a b c
    exact h a b c
    done

  /- Elements in Fin n, which is how we are representing Cn, are defined as a
  natural number x, along with a proof that x < n. Fin n also has many of
  the properties we need to show already proven. -/
  id := {val := 0, isLt := Fin.size_pos'}

  /- Try to prove the other group axioms. If you are struggling, similar proofs
  to the proof for op_assoc can work for the other axioms.-/
  op_id := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    exact Fin.add_zero a
    -- END OF SAMPLE SOLUTION

  id_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    have h : ∀ (a : Fin n), 0 + a = a
    exact fun a => Fin.zero_add a
    exact h a
    -- END OF SAMPLE SOLUTION

  inv := fCn_inv n

  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    have h : ∀ (a : Fin n), -a + a = 0
    exact fun a => neg_add_self a
    exact h a
    -- END OF SAMPLE SOLUTION
