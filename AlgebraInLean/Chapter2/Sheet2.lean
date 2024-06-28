import Mathlib.Tactic

namespace Sheet2

-- ## Things we want to include in this Sheet2

-- - _Modular arithmetic interlude!_

-- Examples of group homomorphisms & isomorphisms
-- - Z/nZ is isomorphic to Cₙ
-- - Any two cyclic groups of the same order are isomorphic

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
-- the previous chapter, as the group of rotational symmetries of an n-gon.

-- Let's look at it through a different lens. C₃ is "the cyclic group of order
-- 3". A cyclic group is one that is generated by a single element. In effect,
-- it is the group you get by applying a non-identity element, say g, to
-- itself. For example, the elements of the cyclic group of order 4 can be
-- written {𝕖, g, g², g³}. Note that we can write the element 𝕖 as g⁰. g is
-- then referred to as the "generator" of the group, and the group generated by
-- an element g can be written <g>. You'll learn more about generators in
-- Chapter 2.

-- We'll use the definition of Cn that you've seen in Chapter 1. Hopefully,
-- you've already proved that it is a group, so we're good to go.

def Cn (n : ℕ): Type := Fin n
def fCn (n : ℕ) : (Cn n) → (Cn n) → (Cn n) := Fin.add

-- We introduce a closely related group; the integers _modulo_ some natural
-- number n. We write this as ℤ/nℤ, for reasons that will become apparent when
-- you eventually come across "quotient groups". We pronounce ℤ/nℤ as "Z mod n
-- Z".

variable (G : ZMod n) (generators : Finset (ZMod n))

#check (ZMod 4 : Type)
#print ZMod

def ZModnZ (n : ℕ) : Type := ZMod n

-- def x : (ZModnZ 3) := 2

#print ZModnZ

-- ## EXERCISES:

-- TODO: Show that a map φ : n → gⁿ is a homomorphism from ℤ/3ℤ to C₃.

-- theorem mod3_hom_to_cyclic3 [Group G] (Z3 : ZMod n) (g : G) (φ : G → Z3) : Homomorphism φ := by

-- TODO: Show that a map φ : n → gⁿ is an isomorphism from ℤ/3ℤ to C₃.

-- theorem mod3_iso_to_cyclic3 [Group G] (Z3 : ZMod n) (g : G) (φ : G → Z3) : Isomorphism φ := by

-- TODO: Generalise the above: ℤ/nℤ is isomorphic to Cₙ, with the map being the
-- same.

-- theorem modn_iso_to_cyclicn [Group G] (Z3 : ZMod n) (g : G) (φ : G → Z3) : Isomorphism φ := by

/- ... -/

-- ## Automorphisms


end Sheet2
