import «AlgebraInLean».Chapter2.Sheet0
import AlgebraInLean.Basic
import Mathlib.Tactic

namespace Defs

  /-

  # Morphisms

  Morphisms are structure-preserving maps between objects in a category. In category theory,
  morphisms are arrows between objects and adhere to certain composition and identity rules.

  Examples of morphisms you may have seen before are functions between sets, homomorphisms between
  algebraic structures, continuous functions between topological spaces, etc.

  But before we dive into morphisms, we prove a few useful theorems about group elements.

  -/

  namespace Interlude

    /-- For all a, b, c ∈ G, ab = ac → b = c-/
    theorem mul_left_eq [Group G] (a b c : G) (h : μ a b = μ a c) : b = c
    :=
      calc
        b = μ 𝕖 b := by rw [id_op]
        _ = μ (μ (ι a) a) b := by rw [← inv_op a]
        _ = μ (ι a) (μ a b) := by rw [op_assoc]
        _ = μ (ι a) (μ a c) := by rw [h]
        _ = μ (μ (ι a) a) c := by rw [op_assoc]
        _ = μ 𝕖 c := by rw [inv_op a]
        _ = c := by rw [id_op]

    /-

    `calc`, like `have`, is an example of what is called "forward reasoning" in Lean. Usually with
    tactic-style proofs, we are trying to go backwards, transforming our goal to one of our assumed
    hypotheses. With forward reasoning, we are trying to transform our assumptions into the goal.

    `calc` might be more familiar than you think, since it closely reflects some pen-and-paper
    proofs via a chain of equalities and algebraic manipulations. Hover over `calc` to see the
    syntax.

    -/

    /- For all g ∈ G, (g⁻¹)⁻¹ = g -/
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

    /- For all a, b ∈ G, a⁻¹ = b⁻¹ → a = b -/
    example [Group G] : ∀ a b : G, ι a = ι b → a = b := by
      intro a b
      intro hinv
      have hinj : ∀ (g : G), ι (ι g) = g
      · apply inv_inv_eq_self
      rw [← hinj a, ← hinj b]
      rw [hinv]

    /-- The inverse function is injective-/
    theorem inv_inj [Group G]: Injective (ι: G → G) := by
      unfold Injective
      have hinv : ∀ (x : G), ι (ι x) = x
      · intro x
        rw [inv_inv_eq_self x]
      intro a b hab
      rw [← hinv a, ← hinv b, hab]

    /-

    `unfold` does what it sounds like: unfolding a symbol to its underlying definition. It isn't
    best practice; it's usually better to write a definition to use `rw` with. However, for a
    one-off use-case, `unfold` suffices.

    You saw the following examples in Sheet 0, but in a much different way.
    It may be useful to review different approaches for the following proofs:

    -/

    -- An injective and surjective function is bijective
    example (f : α → β) (h1 : Injective f) (h2 : Surjective f)
    : (Bijective f) := by
      rw [Bijective]
      constructor
      · assumption -- or `exact h1`
      · assumption -- or `exact h2`

    -- This proof is a bit more involved, so there will be additional commentary in the solutions

    -- The composition of surjective functions is surjective
    example (f : α → β) (g : β → γ) (h1: Surjective f) (h2 : Surjective g)
    : Surjective (g ∘ f) := by
      rw [Surjective] at *
      /- The asterisk represents a 'wildcard', more technically known as a Kleene star. `at *`
      simply means to execute the tactic everywhere possible. -/
      intro y
      /- We want to show that `g ∘ f` is surjective, i.e. that for all y in γ, there exists an x in α
      such that `g ∘ f` equals y; since g is surjective, we use the `have` tactic to express
      something we know must be true and to use it as a hypothesis. -/
      have hx : ∃ (x : β), g x = y := h2 y
      obtain ⟨x, hx⟩ := hx
      obtain ⟨a, hfa⟩ := h1 x
      use a
      change g (f a) = y
      /- `change` allows us to zhuzh the goal into something _definitionally equivalent_, which can
      make it more convenient to apply hypotheses -/
      rw [hfa]
      exact hx

    /-

    ## GROUP MORPHISMS

    Given a group G and a group H, a group homomorphism (_group_ usually omitted) is a map φ from G
    to H which "preserves", or "respects" the group structure. That is, given an element g ∈ G and h
    ∈ H,

    φ(gh) = φ(g)φ(h).

    In other words, you can combine g and h in G, and then apply φ, or apply φ to g and h each,
    before combining them in H. We omit the symbol for the group operator for the sake of
    simplicity.

    An isomorphism has a slightly stricter definition in that φ is required to be a bijection. When
    two groups are isomorphic to each other, they are indistinguishable from each other by structure
    alone. This is often expressed via the phrase "equal up to isomorphism". We'll talk more about
    isomorphisms in the next sheet!

    -/
    def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ
    a) (φ b) = φ (μ a b)

    theorem homomorphism_def [Group G] [Group H] (φ : G → H) : Homomorphism φ ↔ ∀
    (a b : G), μ (φ a) (φ b) = φ (μ a b) := by rfl

    def Isomorphism [Group G] [Group H] (φ : G → H) : Prop := (Homomorphism φ ∧
    Bijective φ)

    /-

    Part of what we mean when we say a homomorphism "respects the group structure" is that
    homomorphisms (and therefore isomorphisms) map inverses elements of group G to corresponding
    inverse elements of group H. We will explore this and examples like these in the following
    exercise.

    Below are some basic proofs of homomorphisms: that they map identities to identities, and
    inverses to inverses.

    -/
    theorem hom_id_to_id [Group G] [Group H] (φ : G → H) (hp :
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

  --To prove this, we first show that if a * b = 𝕖, then b = ι a.

  /-- For all a, b ∈ G, ab = 1 → b = a⁻¹ -/
  theorem two_sided_inv [Group G] (a b : G) (h1 : μ a b = 𝕖): b = ι a := by
    have hq : ∀ (a : G), μ (ι a) a = μ a (ι a)
    · intro g
      rw [inv_op g]
      rw [op_inv g]
    specialize hq a
    have hp : μ a b = μ a (ι a)
    · rw [h1, op_inv]
    rw [mul_left_eq a b (ι a) hp]

  /-

  Note that the inverse of a group element is also the element's unique inverse. Why? (Hint:
  Remember the inverse map is injective, as we proved earlier in the sheet.)

  -/

  /-- Suppose φ : G → H is a homomorphism. If g ∈ G, then φ(g⁻¹) = φ(g)⁻¹ -/
  theorem hom_inv_to_inv [Group G] [Group H] (φ : G → H) (hp :
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


end Interlude

end Defs

/-

You have two options on where to go next. If you're familiar with basic modular arithmetic
(including gcds, lcms, and the Euclidean algorithm), you can go straight to Sheet2. If you would
like a refresher, or simply to see how these concepts are implemented in Lean, feel free to go to
the sheet named `ModularArithmetic.lean`.

-/
