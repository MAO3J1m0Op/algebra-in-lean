import «AlgebraInLean».Basic

namespace Defs

namespace Morphisms

  section Maps
    universe u₁ u₂ u₃
    -- In Lean's type theory, the Calculus of Constructions, there is an infinite
    -- hierarchy of types that contain one another. Type 0 (or simply just "Type"
    -- is contained in Type 1, Type 1 is contained in Type 2, and so on. A type
    -- can never contain itself; if that were to happen, we would run into a
    -- logical paradox! We classify types using what are called "universes"; in
    -- other words, a universe is a family of types. For more information on
    -- Lean's type system, see
    -- https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html.

    variable {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃}
    -- Type n is syntactic sugar for Sort (n + 1). Sort 0 is the bottom of the
    -- hierarchy; expressed as a Type, it would theoretically be written "Type
    -- -1". Using "Sort" allows for a bit more freedom for the range of types. In
    -- this case, you are free to think of α, β, and γ as sets.

    -- Surjectivity, injectivity, and bijectivity of maps
    def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y
    -- Otherwise known as "one-to-one".

    -- We have already seen many injective functions. One of them is the
    -- function which takes any group element to its inverse! (This is actually
    -- bidirectional.)

    example [Group G] : ∀ a b : G, ι a = ι b → a = b:= by
      intro a b
      intro hinv
      have hinj : ∀ (g : G), ι (ι g) = g -- probably shows up in earlier chapter
      · sorry
      rw [← hinj a, ← hinj b]
      rw [hinv]

    def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y
    -- Otherwise known as "onto".

    def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)

    -- It can be instructive to think about bijectivity with regards to function
    -- composition. In Lean, function composition is `∘`. (Type `\circ`.)

    -- Let's prove a few basic consequences of function composition.

    example (f : X → Y) (g : Y → Z) (h1: Surjective f) (h2 : Surjective g)
    : Surjective (g ∘ f) := by
       sorry

    example (f : X → Y) (g : Y → Z) (h1: Injective f) (h2 : Injective g)
    : Injective (g ∘ f) := by
       sorry

    example (f : X → Y) (g : Y → Z) (h1 : Injective (g ∘ f)) (h2 : Injective f)
    : Injective g := by
       sorry

  end Maps

  -- Given a group G and a group H, a homomorphism is a map φ from G to H
  -- which "preserves", or "respects" the group structure. I.e., given an
  -- element g ∈ G and h ∈ H,

  -- φ(gh) = φ(g)φ(h).

  -- An isomorphism has a slightly stricter definition in that φ is required
  -- to be a bijection. When two groups are isomorphic to each other, they are
  -- indisguishable from each other by structure alone. There are various
  -- examples of this correspondence: for example, homomorphisms (and
  -- therefore isomorphisms) map inverses elements of group G to corresponding
  -- inverse elements of group H. We will explore this and examples like these
  -- in the following exercise.

  -- Morphisms
  def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ
  a) (φ b) = φ (μ a b)

  def Isomorphism [Group G] [Group H] (φ : G → H) : Prop := (Homomorphism φ ∧
  Bijective φ)

  -- TODO: Should we define homs/isos with `def` (like above)  or with type
  -- classes (like below?)

  structure group_hom [Group G] [Group H] (φ : G → H) :=
      (hom_map : G → H)
      (hom_mul : ∀ a b, φ (μ a b) = μ (φ a) (φ b))

  structure group_iso [Group G] [Group H] (φ : G → H) extends group_hom φ :=
      (is_bijective : Bijective φ)

  -- As expected, you can see how the process of proving isomorphisms in Lean
  -- might closely parallel pen-and-paper proofs: you split the definition of
  -- an isomorphism into its respective parts via a logical conjunction (or
  -- type class definition): (1) it is a homomorphism, and (2) it is a
  -- bijection, and then prove each part.

  -- Below are some basic proofs of homomorphisms: that they map inverses to
  -- inverses, and identities to identities.

  -- TODO: Broken sketches. Probably missing something obvious; there is an
  -- issue with overloading μ for two different groups
  theorem hom_id_to_id {G H : Type*} [Group G] [Group H] (φ : G → H) (hp :
  Homomorphism φ) (𝕖 : G) (𝕖' : H): φ 𝕖 = 𝕖' := by
      have h1 : φ 𝕖 = φ (μ 𝕖 𝕖)
      · sorry
      have h2 : μ (φ 𝕖) (φ 𝕖) = μ 𝕖' 𝕖'
      · sorry
      have h3 : μ 𝕖' 𝕖' = 𝕖'
      · sorry
      done

  theorem hom_inv_to_inv {G H : Type*} [Group G] [Group H] (φ : G → H) (hp :
  group_hom φ) (g : G) (𝕖 : G) (𝕖' : H) : φ (ι g) = ι (φ g) := by
      have h1 : μ (φ g) (φ (ι g)) = φ (μ g (ι g))
      · sorry
      have h2 : φ (μ g (ι g)) = φ (𝕖)
      · sorry
      have h3 : φ (𝕖) = 𝕖'
      · sorry
      done

  -- Tip: Since the only thing we know about a homomorphism φ is that φ (μ a b)
  -- = μ (φ a) (φ b), it is often instructive to start proofs by applying the
  -- inverse or the identity to an arbitrary element of the group, to exploit
  -- the "multiplicativity" of homomorphisms.

  -- TODO: Maybe add more basic exercises with homs... unsure of what exactly
  -- though

  end Morphisms

end Defs
