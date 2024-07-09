import AlgebraInLean.World01.Sheet6

namespace AlgebraInLean

/-
The last groups we will cover in this chapter are the symmetric groups. This is defined by the
different ways of permuting n elements. The group operation is composition. For example, S₃ has 6
elements, which permute (1, 2, 3) into (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), and
(3, 2, 1). Elements in Sₙ can also be thought of as bijections (invertible functions) from a set of
n elements to itself. We define Sₙ as a function from Fin n to Fin n, along with a proof that it is
bijective (note that the group structure of Fin n is not relevant here).
-/

/-- A symmetric group is a bijection Fin n → Fin n -/
def Symmetric (n : ℕ) : Type := {f : Fin n → Fin n // Function.Bijective f}

variable {n : ℕ}


/--
Two elements of the same symmetric group are equal when the underlying functions are the same.
-/
@[ext] -- this allows the "ext" tactic to work on elements of Sₙ
theorem Symmetric.ext {n : ℕ} {f g : Symmetric n} (h : f.val = g.val) : f = g := by
  unfold Symmetric at *
  ext : 1
  exact h
  done


/--
The group operation is function composition, along with a proof that the composition of two
bijective functions is also bijective.
-/
protected def Symmetric.op (f g : Symmetric n) : Symmetric n where
  val := f.val ∘ g.val
  property := Function.Bijective.comp f.prop g.prop


/-- The inverse of an element of Sₙ is just the inverse of the underlying function. -/
protected noncomputable def Symmetric.inv (f : Symmetric n) : Symmetric n := by
  -- `choose` invokes the axiom of choice (see `Classical.choose` and `Classical.choose_spec`)
  choose g h using Function.bijective_iff_has_inverse.mp f.prop
  use g
  apply Function.bijective_iff_has_inverse.mpr
  use f.val
  exact h.symm
  done

/-
This theorem allows for easier use of `.inv` defined above so you do not have to dig into how the
`choose` tactic works.
-/
protected theorem Symmetric.inv_spec (f : Symmetric n)
  : Function.LeftInverse f.inv.val f.val ∧ Function.RightInverse f.inv.val f.val :=
  Classical.choose_spec (Function.bijective_iff_has_inverse.mp f.prop)


noncomputable instance (n : ℕ) : Group (Symmetric n) where
  op := Symmetric.op

  op_assoc a b c := by
    -- sorry
    -- SAMPLE SOLUTION
    rfl
    -- END OF SAMPLE SOLUTION

  id := by
    use id
    exact Function.bijective_id

  op_id a := by
    -- sorry
    -- SAMPLE SOLUTION
    rfl
    -- END OF SAMPLE SOLUTION

  id_op a := by
    -- sorry
    -- SAMPLE SOLUTION
    rfl
    -- END OF SAMPLE SOLUTION

  inv := Symmetric.inv

  /-
  Proving this is more involved than the others. If you get stuck, try using the
  `Symmetric.inv_spec` theorem, the `ext` tactic, and looking at the proofs in the other sheets for
  help.
  -/
  inv_op a := by
    -- sorry
    -- SAMPLE SOLUTION
    ext : 1
    simp only [μ, Symmetric.op, 𝕖, Symmetric.inv]
    apply Function.LeftInverse.comp_eq_id
    exact a.inv_spec.left
    -- END OF SAMPLE SOLUTION
