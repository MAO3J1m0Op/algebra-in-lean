import AlgebraInLean.World01.Sheet2

namespace AlgebraInLean

-- This allows us to not have to say [Group G] when stating all the theorems below.
variable {G : Type*} [Group G]

/- When we defined groups, we only required existance of an identity and inverses. This means that
there could be multiple identities and inverse functions. However, this is not possible, and we can
show that the identity and inverse are unique. -/

/- Since the proof of op_inv used the previous definition of Group, we need to reprove it using the
new definitions. -/
theorem op_inv (a : G) : μ a (ι a) = 𝕖 := by
  rw [←(id_op (μ a (ι a))), ←(inv_op (ι a))]
  rw [op_assoc, ←(op_assoc (ι a) a (ι a)), inv_op, id_op]


/- This proves that the identity is unique. This theorem only requires G to be a monoid, so that is
all we will assume. The obtain tactic may be useful for dealing with the and as a hypothesis. When
h is a hypothesis of P ∧ Q, obtain ⟨h1, h2⟩ := h creates hypotheses h1 and h2 which state P and Q
respectively. -/
theorem id_unique [Monoid M] (e2 : M) : (∀ a : M, (μ a e2 = a ∧ μ e2 a = a)) → e2 = 𝕖 := by
  -- sorry
  -- SAMPLE SOLUTION
  intro ha
  specialize ha 𝕖
  obtain ⟨ha1, ha2⟩ := ha
  rw [id_op] at ha1
  exact ha1
  -- END OF SAMPLE SOLUTION

/- This proves that inverses are unique. -/
theorem inv_unique (a i : G) : (μ a i = 𝕖 ∧ μ i a = 𝕖) → i = ι a := by
  -- sorry
  -- SAMPLE SOLUTION
  intro ha
  obtain ⟨ha1, _⟩ := ha
  rw [←(op_id (ι a)), ←ha1, ←(op_assoc (ι a) a i), inv_op, id_op]
  -- END OF SAMPLE SOLUTION

/- Now that we have the uniqueness theorems, we can prove some more interesting theorems about the
identity and inverses. -/
theorem shoes_and_socks (a b : G) : ι (μ a b) = μ (ι b) (ι a) := by
  -- sorry
  -- SAMPLE SOLUTION
  symm
  apply inv_unique
  constructor
  · rw[op_assoc, ←(op_assoc b (ι b) (ι a)), op_inv, id_op, op_inv]
  · rw[op_assoc, ←(op_assoc (ι a) a b), inv_op, id_op, inv_op]
  -- END OF SAMPLE SOLUTION

theorem inv_inv (a : G) : ι (ι a) = a := by
  --sorry
  -- SAMPLE SOLUTION
  symm
  apply inv_unique
  constructor
  · exact inv_op a
  · exact op_inv a
  -- END OF SAMPLE SOLUTION

theorem right_cancel (a b c : G) : μ b a = μ c a → b = c := by
  -- sorry
  -- SAMPLE SOLUTION
  intro h
  rw[←(op_id b), ←(op_id c), ←(op_inv a), ←op_assoc, ←op_assoc, h]
  -- END OF SAMPLE SOLUTION
