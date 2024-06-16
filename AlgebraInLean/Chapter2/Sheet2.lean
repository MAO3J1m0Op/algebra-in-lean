import «AlgebraInLean».Basic

-- Examples of group homomorphisms

/-

Like many other things in abstract algebra, you will find that you have seen
homomorphisms before, even if you weren't aware that they _were_ homomorphisms.
For example, the determinant of an n × n Real matrix is a homomorphism from the
group GL_n(ℝ) to (ℝ, *). Recall the group axioms and convince yourself this is
the case.

-/

#eval (add_one ∘ times_two) 3

