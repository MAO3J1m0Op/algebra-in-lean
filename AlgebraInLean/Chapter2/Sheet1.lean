import «AlgebraInLean».Basic

-- TODO: Clean up *Maps* section; some of the content overlaps with Sheet 0

namespace Defs

namespace Morphisms

    -- # Morphisms
    -- Morphisms are structure-preserving maps between objects in a category.
    -- In category theory, morphisms are arrows that connect objects and adhere
    -- to certain composition and identity rules.

    -- Examples of morphisms you may have seen before are functions between
    -- sets, homomorphisms between algebraic structures, continuous functions
    -- between topological spaces, etc.

    -- But before we dive into morphisms, we present a quick interlude about
    -- maps!

  section Maps
    universe u₁ u₂ u₃
    -- Brace yourself for a type theory interlude!
    -- In Lean's type theory, the Calculus of Constructions, there is an
    -- infinite hierarchy of types that contain one another. Type 0 (or simply
    -- just "Type" is contained in Type 1, Type 1 is contained in Type 2, and
    -- so on. A type can never contain itself; if that were to happen, we would
    -- run into a logical paradox! We classify types using what are called
    -- "universes"; in other words, a universe is a family of types. For more
    -- information on Lean's type system, see
    -- https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html.

    variable {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃}
    -- You are free to think of α, β, and γ as sets.

    def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y
    -- Otherwise known as "one-to-one".

    -- We have already seen many injective functions. One of them is the
    -- function which takes any group element to its inverse!

    -- To do this, we need to prove two intuitive propositions: First, a simple
    -- group identity. Then, a proof that given a group G and an element g in
    -- G, the inverse of the inverse of g is g itself. In other words, the
    -- inverse cancels itself out.

    theorem mul_left_eq [Group G] (a b c : G) (h : μ a b = μ a c) : b = c
    :=
      calc
        b = μ 𝕖 b := by rw [id_op]
        _ = μ (μ (ι a) a) b := by rw [← inv_op a]
        _ = μ (ι a) (μ a b) := by rw [Semigroup.op_assoc]
        _ = μ (ι a) (μ a c) := by rw [h]
        _ = μ (μ (ι a) a) c := by rw [Semigroup.op_assoc]
        _ = μ 𝕖 c := by rw [inv_op a]
        _ = c := by rw [id_op]

    theorem inv_inv_eq_self [Group G] : ∀ g : G, ι (ι g) = g := by
      intro g
      have hq : ∀ (a : G), μ (ι a) a = μ a (ι a)
      · intro a
        rw [inv_op a]
        rw [op_inv a]
      specialize hq (ι g)
      rw [inv_op (ι g)] at hq
      symm at hq
      rw [← inv_op g] at hq
      rw [mul_left_eq (ι g) (ι (ι g)) g hq]

    example [Group G] : ∀ a b : G, ι a = ι b → a = b := by
      intro a b
      intro hinv
      have hinj : ∀ (g : G), ι (ι g) = g
      · apply inv_inv_eq_self
      rw [← hinj a, ← hinj b]
      rw [hinv]

    theorem inv_inj [Group G]: Injective (ι: G → G) := by
      unfold Injective
      have hinv : ∀ (x : G), ι (ι x) = x
      · intro x
        rw [inv_inv_eq_self x]
      intro a b hab
      rw [← hinv a, ← hinv b, hab]

    def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y
    -- Otherwise known as "onto".

    def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)
    -- Also known as "one-to-one"!

    -- It can be instructive to think about bijectivity with regards to
    -- function composition. In Lean, function composition is `∘`. (Type
    -- `\circ`.)

    -- Let's prove a few basic consequences of function composition.

    -- This is simply restating the definition!
    example (f : α → β) (h1 : Injective f) (h2 : Surjective f)
    : (Bijective f) := by
      unfold Bijective
      constructor
      assumption -- or `exact h1`
      assumption -- or `exact h2`

    -- This proof is a bit more of a challenge, so there will be additional
    -- commentary in the solutions.
    example (f : α → β) (g : β → γ) (h1: Surjective f) (h2 : Surjective g)
    : Surjective (g ∘ f) := by
      unfold Surjective at *
      -- The asterisk represents a 'wildcard', more technically known as a
      -- Kleene star. `at *` simply means to execute the tactic everywhere
      -- possible.
      intro y
      -- We want to show that `g ∘ f` is surjective, i.e. that for all y in γ,
      -- there exists an x in α such that `g ∘ f` equals y; since g is
      -- surjective, we use the `have` tactic to express something we know must
      -- be true and to use it as a hypothesis
      have hx : ∃ (x : β), g x = y := h2 y
      cases' hx with x' hx'
      obtain ⟨a, hfa⟩ := h1 x'
      use a
      change g (f a) = y -- `change` allows us to zhuzh the goal into something _definitionally equivalent_
      rw [hfa]
      exact hx'

  end Maps

  -- Given a group G and a group H, a group homomorphism (_group_ usually
  -- omitted) is a map φ from G to H which "preserves", or "respects" the group
  -- structure. I.e., given an element g ∈ G and h ∈ H,

  -- φ(gh) = φ(g)φ(h).

  -- An isomorphism has a slightly stricter definition in that φ is required to
  -- be a bijection. When two groups are isomorphic to each other, they are
  -- indistinguishable from each other by structure alone. This is often
  -- expressed via the phrase "equal up to isomorphism".

  -- Morphisms
  def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ
  a) (φ b) = φ (μ a b)

  theorem homomorphism_def [Group G] [Group H] (φ : G → H) : Homomorphism φ ↔ ∀ (a b : G), μ (φ a) (φ b) = φ (μ a b) := by
    rfl

  def Isomorphism [Group G] [Group H] (φ : G → H) : Prop := (Homomorphism φ ∧
  Bijective φ)

  -- Part of what we mean when we say a homomorphism "respects the group
  -- structure" is that homomorphisms (and therefore isomorphisms) map inverses
  -- elements of group G to corresponding inverse elements of group H. We will
  -- explore this and examples like these in the following exercise.

  -- Below are some basic proofs of homomorphisms: that they map identities to
  -- identities, and inverses to inverses.

  theorem hom_id_to_id {G H : Type*} [Group G] [Group H] (φ : G → H) (hp :
  Homomorphism φ) (a : G) : φ 𝕖 = 𝕖 := by
    have h1 : φ (μ 𝕖 𝕖) = μ (φ 𝕖) (φ 𝕖) := by
      rw [homomorphism_def] at hp
      specialize hp 𝕖 𝕖
      exact hp.symm
    have h2 : μ (φ 𝕖) 𝕖 = μ (φ 𝕖) (φ 𝕖) := by
      rw [op_id]
      nth_rewrite 1 [← op_id 𝕖]
      exact h1
    have h3 : 𝕖 = φ 𝕖 := by
      rw [mul_left_eq (φ 𝕖) 𝕖 (φ 𝕖)]
      exact h2
    exact h3.symm

  -- To prove this, we first show that if a * b = 𝕖 and b * a = 𝕖, then b = ι a.
  theorem two_sided_inv [Group G] (a b : G) (h1 : μ a b = 𝕖) (h2 : μ b a = 𝕖) : b = ι a := by
    have hq : ∀ (a : G), μ (ι a) a = μ a (ι a)
    · intro g
      rw [inv_op g]
      rw [op_inv g]
    specialize hq a
    have hp : μ a b = μ a (ι a)
    · rw [h1, op_inv]
    rw [mul_left_eq a b (ι a) hp]

  theorem hom_inv_to_inv {G H : Type*} [Group G] [Group H] (φ : G → H) (hp :
  Homomorphism φ) (g : G) : φ (ι g) = ι (φ g) := by
    have h1 : μ (φ (ι g)) (φ g) = φ (μ (ι g) g)
    · rw [homomorphism_def] at hp
      rw [hp (ι g) g]
    have h2 : φ (μ (ι g) g) = φ 𝕖
    · rw [inv_op]
    rw [h2] at h1
    rw [hom_id_to_id φ hp g] at h1
    rw [two_sided_inv (φ (ι g)) (φ g) h1]
    rw [inv_inv_eq_self]
    calc
      μ (φ g) (φ (ι g)) = φ (μ g (ι g)) := by rw [hp g (ι g)]
      _ = φ 𝕖 := by rw [op_inv]
      _ = 𝕖 := by rw [hom_id_to_id φ hp g]

  end Morphisms

end Defs
