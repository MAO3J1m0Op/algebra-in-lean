import AlgebraInLean.Basic
import AlgebraInLean.Chapter2.Sheet1
import Mathlib.Tactic

namespace Sheet2

namespace Defs

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

-- We'll use the definition of Cₙ that you've seen in Chapter 1. Hopefully,
-- you've already proved that it is a group, so we're good to go.

def Cn (n : ℕ): Type := Fin n
def fCn (n : ℕ) : (Cn n) → (Cn n) → (Cn n) := Fin.add
def inv_fCn (n : ℕ) : (Fin n) → (Fin n) := fun x => -x

-- We introduce a closely related group; the integers _modulo_ some natural
-- number n. The definition is virtually identical. We write this as ℤ/nℤ, for
-- reasons that will become apparent when you eventually come across _quotient
-- groups_. We pronounce ℤ/nℤ as "Z mod n Z".

def ZModnZ (n : ℕ) : Type := Fin n
def fZModnZ (n : ℕ) : (ZModnZ n) → (ZModnZ n) → (ZModnZ n) := Fin.add
def inv_ZModnZ (n : ℕ) : (Fin n) → (Fin n) := fun x => -x

-- The similarity between Cₙ and ℤ/nℤ might lead one to ask: are they
-- isomorphic? In order to answer that excellent question, let's prove a more
-- lenient result and work our way up to isomorphism:

-- TODO: Consider scrapping everything here and look at more abstract examples of isomorphism. Why? Maybe a better idea to introduce ℤ/nℤ when quotient groups are introduced... also, formally considering isomorphisms between groups requires considering orders or elements. :(

-- TODO: Show that a map φ : n → gⁿ is a homomorphism from ℤ/3ℤ to C₃.

theorem mod3_hom_to_cyclic3 (C3 : Defs.Group (Cn 3)) (Z3 : Defs.Group (ZModnZ 3)) (g : G) (φ : C3 → Z3) : Homomorphism φ := by
  sorry

-- TODO: Show that a map φ : n → gⁿ is an isomorphism from ℤ/3ℤ to C₃.

theorem mod3_iso_to_cyclic3 (C3 : Defs.Group (Cn 3)) (Z3 : Defs.Group (ZModnZ 3)) (g : G) (φ : C3 → Z3) : Isomorphism φ := by
  sorry

-- TODO: Generalise the above: ℤ/nℤ is isomorphic to Cₙ, with the map being the
-- same.

theorem modn_iso_to_cyclicn (Cn : Defs.Group (Cn n)) (Zn : Defs.Group (ZModnZ n)) (g : G) (φ : Cn → Zn) : Isomorphism φ := by
  sorry

/- ... -/

