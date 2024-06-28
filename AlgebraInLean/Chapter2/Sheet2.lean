import Mathlib.Tactic

namespace Sheet2

-- ## Things we want to include in this Sheet2

-- Examples of group homomorphisms & isomorphisms
-- - Z/nZ is isomorphic to Cₙ
-- - Any two cyclic groups of the same order are isomorphic
-- - 

-- Definition of automorphism, (and hence endomorphism?)
-- Mention familiar examples (not formalized): linear transformations between
-- vector spaces, functions (like graphs you see in high school math),
-- permutations

-- Conjugation is an automorphism
-- Which segues us very nicely into the next sheet, which probably will be
-- about automorphism groups

/- ---------- -/

-- ## Homomorphisms and Isomorphisms

-- Like many other things in abstract algebra, you will find that you have seen
-- homomorphisms before, even if you weren't aware that they _were_
-- homomorphisms. For example, the determinant of an n × n Real matrix is a
-- homomorphism from the group GL_n(ℝ) to (ℝ, *).

-- Below, we provide other examples of homomorphisms and isomorphisms with
-- concrete examples of groups that you have already seen before in Chapter 1.

-- We formally introduce the notion of a cyclic group. You have seen this in
-- the previous chapter, just through a different lens; C₃ is the cyclic group
-- of order 3. A cyclic group is one that is generated by a single element. In
-- effect, it is the group you get by applying a non-identity element, say g,
-- to itself. For example, the elements of the cyclic group of order 4 can be
-- written {e, g, g², g³}. Note that we can write the element e as g⁰. g is
-- then referred to as the "generator" of the group, and the group generated by
-- an element g can be written <g>.

-- Lean already has machinery behind cyclic groups, referred to generally as Cₙ
-- where n is the order of the group:

class isCyclic (α : Type u) [Group α] : Prop where
  exists_generator : ∃ (g : α), ∀ (x : α), x ∈ Subgroup.zpowers g

-- Don't worry about the term `Subgroup`, this will be defined very soon!
-- However, we can see that `zpowers` clearly refers to taking multiplicative
-- integer powers of a group element g, which tracks with our definition above. 

-- We introduce a closely related group; the integers _modulo_ some integer n.

variable (G : ZMod n) (generators : Finset (ZMod n))

-- ## EXERCISES:

-- TODO: Show that a map φ : n → gⁿ is a homomorphism from ℤ/3ℤ to C₃.

-- theorem mod3_hom_to_cyclic3 [Group G] (Z3 : ZMod n) (g : G) (φ : G → Z3) : Homomorphism φ := by

-- TODO: Show that a map φ : n → gⁿ is an isomorphism from ℤ/3ℤ to C₃.

-- theorem mod3_iso_to_cyclic3 [Group G] (Z3 : ZMod n) (g : G) (φ : G → Z3) : Isomorphism φ := by

-- TODO: Generalise the above: ℤ/nℤ is isomorphic to Cₙ, with the map being the
-- same.

-- theorem modn_iso_to_cyclicn [Group G] (Z3 : ZMod n) (g : G) (φ : G → Z3) : Isomorphism φ := by

/- ---------- -/

-- ## Automorphisms

-- To define an automorphism, we first take a look at the more general
-- endomorphism. An endomorphism (and morphisms in general) can be defined
-- among many different types of mathematical objects, but in AlgebraInLean it
-- will always refer to a group endomorphism.

-- A group endomorphism is a homomorphism from a group G _to itself_. An
-- automorphism is an endomorphism that is also a bijection.

-- def Endomorphism 

-- You can think of it like a permutation from a group to itself, although it
-- is important that this permutation respects the group structure.
-- see more specifically what "respecting the group structure" looks like in
-- the next chapter (keep an eye out for orders!).

-- TODO: Do we provide toy examples of automorphisms? Or do we define
-- conjugation and then go straight into proving that conjugation is an
-- automorphism?

end Sheet2
