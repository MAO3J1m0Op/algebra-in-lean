import «AlgebraInLean».Basic

namespace Defs  

namespace Morphisms

  universe u₁ u₂ u₃
  /- In Lean's type theory, the Calculus of Constructions, there is an infinite
  hierarchy of types that contain one another. Type 0 (or simply just "Type" is
  contained in Type 1, Type 1 is contained in Type 2, and so on. A type can
  never contain itself; if that were to happen, we would run into a logical
  paradox! We classify types using what are called "universes"; in other words,
  a universe is a family of types. For more information on Lean's type system,
  see https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html.
  -/
  variable {a : Sort u₁} {β : Sort u₂} {γ : Sort u₃}
  /- Type n is syntactic sugar for Sort (n + 1). Sort 0 is the bottom of the
  hierarchy; expressed as a Type, it would theoretically be written "Type -1".
  Using "Sort" allows for a bit more freedom for the range of types. In this
  case, you are free to think of α, β, and γ as sets. -/

   -- Surjectivity, injectivity, and bijectivity of maps
   def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y
   -- Otherwise known as "one-to-one".
   
   def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y
   -- Otherwise known as "onto".

   def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)

  /- It can be instructive to think about bijectivity with regards to function
  composition, so let's define composition! -/

  -- def (WIP)

   -- Morphisms
   def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ
   a) (φ b) = φ (μ a b)

   def Isomorphism [Group G] [Group H] (φ : G → H) : Prop := (Homomorphism φ ∧
   Bijective φ)

   /- As expected, you can see how the process of proving isomorphisms in Lean
   closely parallels pen-and-paper proofs: you split the definition of an
   isomorphism into its respective parts via a logical conjunction: (1) it is a
   homomorphism, and (2) it is a bijection, and then prove each part. -/

   /- Below are some basic proofs of homomorphisms: that they map inverses to
   inverses, and identities to identities. -/

   theorem hom_inv_to_inv {G H : Type*} [Group G] [Group H] (φ : G → H) (hp :
   Homomorphism φ) (g : G)
     : φ (Group.inv g) = Group.inv (φ g) := by
       sorry

   -- theorem hom_id_to_id {G H : Type*} [Group G] [Group H] (φ : G → H) (hp :
   -- Homomorphism φ)
   --   : φ id = id := by
   --     sorry (WIP?)

   /- Since the only thing we know about a homomorphism φ is that φ (μ a b) = μ
   (φ a) (φ b), it is often instructive to start proofs by applying the
   inverse or the identity to an arbitrary element of the group, to exploit the
   "multiplicativity" of homomorphisms. -/

  end Morphisms
