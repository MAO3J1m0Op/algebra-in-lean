import AlgebraInLean.Chapter01.Sheet02

namespace AlgebraInLean

variable {α : Type*}

/-
When we defined the monoids and groups, we only required the *existence* of identity and inverses,
but not their uniqueness. However, it does happen that they must be unique, as shown below.
-/

/--
Uniqueness of the identity element in a monoid. If any element e₂ "behaves like" the identity, then
it must be equal to the identity.
-/
theorem id_unique [Monoid α] (e₂ : α) (h : ∀ (a : α), (μ a e₂ = a ∧ μ e₂ a = a)) : e₂ = 𝕖 := by
  /-
  The `obtain` tactic may be useful. Given a hypothesis `h : P ∧ Q`, `obtain ⟨h₁, h₂⟩ := h` creates
  hypotheses `h₁ : P` and `h₂ : Q`. This also works to destructure other types like `∃`.
  -/
  -- sorry
  -- SAMPLE SOLUTION
  specialize h 𝕖
  obtain ⟨h, _⟩ := h -- we don't care about the property on the right, so we use `_` instead.
  rw [id_op] at h
  exact h
  -- END OF SAMPLE SOLUTION

variable [Group α]

/--
Uniqueness of the inverse of an element. If any element i "behaves like" the inverse of a, then it
must be equal to the inverse of a.
-/
theorem inv_unique (a i : α) (h : μ a i = 𝕖 ∧ μ i a = 𝕖) : i = ι a := by
  -- sorry
  -- SAMPLE SOLUTION
  obtain ⟨h, _⟩ := h
  rw [←op_id (ι a), ←h, ←op_assoc (ι a), inv_op, id_op]
  -- END OF SAMPLE SOLUTION

/-
Now that we have the uniqueness theorems, we can prove some more interesting theorems about the
identity and inverses.
-/

/--
(a ⬝ b)⁻¹ = b⁻¹ ⬝ a⁻¹

Colloquially, the "shoes and socks theorem" because you put on your socks before your shoes, but you
take off your shoes before your socks. "Anticommutativity" is the fancy name for this: a function
that "commutes" with the operation but inverts the order of the operands.
-/
theorem inv_anticomm (a b : α) : ι (μ a b) = μ (ι b) (ι a) := by
  -- sorry
  -- SAMPLE SOLUTION
  symm
  apply inv_unique
  constructor
  · rw [op_assoc, ←op_assoc b, op_inv, id_op, op_inv]
  · rw [op_assoc, ←op_assoc (ι a), inv_op, id_op, inv_op]
  -- END OF SAMPLE SOLUTION

/-- (a⁻¹)⁻¹ = a -/
theorem inv_inv (a : α) : ι (ι a) = a := by
  --sorry
  -- SAMPLE SOLUTION
  symm
  apply inv_unique
  constructor
  · exact inv_op a
  · exact op_inv a
  -- END OF SAMPLE SOLUTION

/-- 1⁻¹ = 1 -/
theorem inv_id [Group α] : ι 𝕖 = (𝕖 : α) := by
  -- sorry
  -- SAMPLE SOLUTION
  symm
  apply inv_unique
  constructor
  · exact op_id 𝕖
  · exact op_id 𝕖
  -- END OF SAMPLE SOLUTION

/-- b ⬝ a = c ⬝ a ⇒ b = c -/
theorem right_cancel (a b c : α) (h : μ b a = μ c a) : b = c := by
  -- sorry
  -- SAMPLE SOLUTION
  rw[←op_id b, ←op_id c, ←op_inv a, ←op_assoc, ←op_assoc, h]
  -- END OF SAMPLE SOLUTION
