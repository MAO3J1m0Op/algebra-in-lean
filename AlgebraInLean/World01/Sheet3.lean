import «AlgebraInLean».Basic
open Defs

/- Concretely naming one element of a group as the identity, and having an
inverse function that gives one output gives the impression that the
identity and inverses are unique. This can be proven-/

/- Since the proof of op_inv used the previous definition of Group, we need
to reprove it using the new definition-/
theorem op_inv [Defs.Group G] (a : G) : μ a (ι a) = 𝕖 := by
  rw[(id_op (μ a (ι a))).symm, (inv_op (ι a)).symm]
  rw[op_assoc, (op_assoc (ι a) a (ι a)).symm, inv_op, id_op]


/- This proves that the identity is unique. This theorem only requires G to
be a monoid, so that is all we will assume-/
theorem identity_uniqueness [Defs.Monoid G] (e2 : G) : (∀ a : G, (μ a e2 = a ∧ μ e2 a = a)) → e2 = 𝕖 := by
  -- sorry
  -- SAMPLE SOLUTION
  intro ha
  specialize ha 𝕖
  cases' ha with ha1 ha2
  rw[id_op] at ha1
  exact ha1
  -- END OF SAMPLE SOLUTION

/- This proves that inverses are unique-/
theorem inverse_uniqueness [Defs.Group G] (a i : G) : (μ a i = 𝕖 ∧ μ i a = 𝕖) → i = ι a := by
  -- sorry
  -- SAMPLE SOLUTION
  intro ha
  cases' ha with ha1 ha2
  rw[(op_id (ι a)).symm]
  rw[ha1.symm]
  rw[(op_assoc (ι a) a i).symm]
  rw[inv_op, id_op]
  -- END OF SAMPLE SOLUTION
