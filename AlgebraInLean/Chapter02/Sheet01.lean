import AlgebraInLean.Chapter02.Sheet00

namespace AlgebraInLean

/-

# Morphisms

Morphisms are structure-preserving maps between objects in a category. Think of a category as a
bucket filled with a certain mathematical object (i.e. groups, vector spaces, sets) and their
corresponding morphisms (group homomorphisms, linear transformations, and functions respectively).

In category theory---which is surprisingly the study of categories---morphisms serve as "arrows"
between objects and adhere to certain composition and identity rules.

Examples of morphisms you may have seen before are functions between sets, homomorphisms between
algebraic structures, continuous functions between topological spaces, etc.

But before we dive into morphisms, we prove a few useful theorems about group elements.

-/

variable {G H : Type*} [Group G] [Group H]

/- For all a, b, c ∈ G, ab = ac → b = c -/
theorem mul_left_eq (a b c : G) (h : μ a b = μ a c) : b = c
:=
  -- SAMPLE SOLUTION
  calc
    b = μ 𝕖 b := by rw [id_op]
    _ = μ (μ (ι a) a) b := by rw [← inv_op a]
    _ = μ (ι a) (μ a b) := by rw [op_assoc]
    _ = μ (ι a) (μ a c) := by rw [h]
    _ = μ (μ (ι a) a) c := by rw [op_assoc]
    _ = μ 𝕖 c := by rw [inv_op a]
    _ = c := by rw [id_op]
  -- END SAMPLE SOLUTION
/-

This is a familiar proof from Chapter 1, but this time we're using the very nifty tactic `calc`.

`calc`, like `have`, is an example of what is called "forward reasoning" in Lean. Usually with
tactic-style proofs, we are trying to go backwards, transforming our goal to one of our assumed
hypotheses. With forward reasoning, we are trying to transform our assumptions into the goal.

`calc` might be more easier to work with than you think, since it closely reflects some
pen-and-paper proofs via a chain of equalities and algebraic manipulations. Hover over `calc` to see
the syntax. Don't let it scare you!

-/

/- For all g ∈ G, (g⁻¹)⁻¹ = g -/
theorem inv_inv_eq_self : ∀ g : G, ι (ι g) = g := by
  -- SAMPLE SOLUTION
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
  -- END SAMPLE SOLUTION

/- For all a, b ∈ G, a⁻¹ = b⁻¹ → a = b -/
example : ∀ a b : G, ι a = ι b → a = b := by
  -- SAMPLE SOLUTION
  intro a b
  intro hinv
  have hinj : ∀ (g : G), ι (ι g) = g
  · apply inv_inv_eq_self
  rw [← hinj a, ← hinj b]
  rw [hinv]
  -- END SAMPLE SOLUTION

/- The inverse function is injective -/
theorem inv_inj : Injective (ι: G → G) := by
  -- SAMPLE SOLUTION
  unfold Injective
  have hinv : ∀ (x : G), ι (ι x) = x
  · intro x
    rw [inv_inv_eq_self x]
  intro a b hab
  rw [← hinv a, ← hinv b, hab]
  -- END SAMPLE SOLUTION
/-

`unfold` does what it sounds like: unfolding a symbol to its underlying definition. It isn't best
practice; it's usually better to write a definition to use `rw` with. However, for a one-off
use-case, `unfold` suffices.

You saw the following examples in Sheet 0, but in a much different way. It may be useful to review
different approaches for the following proofs:

-/

variable {α β γ : Type*}

/- An injective and surjective function is bijective -/
example (f : α → β) (h1 : Injective f) (h2 : Surjective f)
: (Bijective f) := by
  rw [Bijective]
  constructor <;> assumption

/-

The `<;>` tactic simply applies and reapplies the following tactic to as many goals as possible. We
could have also written the line as:

``
constructor
· assumption
· assumption
``

-/

/-

You may recognize this proof from the previous sheet. However, this proof makes use of a helpful
tactic you haven't seen before: `change`, as well as the asterisk wildcard. It may be
instructive to take a look at them in action.

-/

/- The composition of surjective functions is surjective -/
example (f : α → β) (g : β → γ) (h₁: Surjective f) (h₂ : Surjective g) : Surjective (g ∘ f) := by
  rw [Surjective] at *
  /-
  The asterisk represents a 'wildcard', more technically known as a Kleene star. `at *` simply
  means to execute the tactic everywhere possible.
  -/
  intro y
  /-
  We want to show that `g ∘ f` is surjective, i.e. that for all y in γ, there exists an x in α
  such that `g ∘ f` equals y; since g is surjective, we use the `have` tactic to express
  something we know must be true and to use it as a hypothesis.
  -/
  have hx : ∃ (x : β), g x = y := h₂ y
  obtain ⟨x, hx⟩ := hx
  obtain ⟨a, hfa⟩ := h₁ x
  use a
  change g (f a) = y
  /-
  `change` allows us to transform the goal into something _definitionally equivalent_, which can
  make it more convenient to apply hypotheses and make things clearer for both the prover and
  the reader.
  -/
  rw [hfa]
  exact hx

/-

## GROUP MORPHISMS

Given a group G and a group H, a group homomorphism (_group_ usually omitted) is a map φ from G to H
which "preserves", or "respects" the group structure. That is, given an element g ∈ G and h ∈ H,

φ(gh) = φ(g)φ(h).

In other words, you can combine g and h in G, and then apply φ, or apply φ to g and h each, before
combining them in H. We omit the symbol for the group operator for the sake of simplicity.

An isomorphism has a stricter definition in that φ is required to be a bijection. When two groups
are isomorphic to each other, they are indistinguishable from each other by structure alone. This is
often expressed via the phrase "equal up to isomorphism". We'll talk more about isomorphisms in the
next sheet!

-/

def Homomorphism (φ : G → H) : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

theorem Homomorphism_def (φ : G → H) : Homomorphism φ ↔ ∀ (a b : G), μ (φ a) (φ b) = φ (μ a b) := by rfl

def Isomorphism (φ : G → H) : Prop := (Homomorphism φ ∧ Bijective φ)

/-

Part of what we mean when we say a homomorphism "respects the group structure" is that homomorphisms
(and therefore isomorphisms) map inverses elements of group G to corresponding inverse elements of
group H. We will explore this and examples like these in the following exercise.

Below are some basic proofs of homomorphisms: that they map identities to identities, and inverses
to inverses.

-/

/- Suppose φ : G → H is a homomorphism. Then φ(e) = e. -/
theorem hom_id_to_id (φ : G → H) (hp : Homomorphism φ) (a : G) : φ 𝕖 = 𝕖 := by
  -- SAMPLE SOLUTION
  have h₁ : φ (μ 𝕖 𝕖) = μ (φ 𝕖) (φ 𝕖) := by
    rw [Homomorphism_def] at hp
    specialize hp 𝕖 𝕖
    exact hp.symm
  have h₂ : μ (φ 𝕖) 𝕖 = μ (φ 𝕖) (φ 𝕖) := by
    rw [op_id]
    nth_rewrite 1 [← op_id 𝕖]
    exact h₁
  have h₃ : 𝕖 = φ 𝕖 := by
    rw [mul_left_eq (φ 𝕖) 𝕖 (φ 𝕖)]
    exact h₂
  exact h₃.symm
  -- END SAMPLE SOLUTION

/-

To prove that homomorphisms take inverses to inverses, first show that if a * b = 𝕖, then b = ι a.

-/

/- For all a, b ∈ G, ab = 1 → b = a⁻¹ -/
theorem two_sided_inv (a b : G) (h1 : μ a b = 𝕖): b = ι a := by
  -- END SAMPLE SOLUTION
  have hq : ∀ (a : G), μ (ι a) a = μ a (ι a)
  · intro g
    rw [inv_op g]
    rw [op_inv g]
  specialize hq a
  have hp : μ a b = μ a (ι a)
  · rw [h1, op_inv]
  rw [mul_left_eq a b (ι a) hp]
  -- END SAMPLE SOLUTION
/-

Note that the inverse of a group element is also the element's unique inverse. Why? (Hint:
Remember the inverse map is injective, as we proved earlier in the sheet.)

-/

/- Suppose φ : G → H is a homomorphism. If g ∈ G, then φ(g⁻¹) = φ(g)⁻¹ -/
theorem hom_inv_to_inv (φ : G → H) (hp : Homomorphism φ) (g : G) : φ (ι g) = ι (φ g) := by
  -- SAMPLE SOLUTION
  have h1 : μ (φ (ι g)) (φ g) = φ (μ (ι g) g)
  · rw [Homomorphism_def] at hp
    rw [hp (ι g) g]
  have h2 : φ (μ (ι g) g) = φ 𝕖
  · rw [inv_op]
  rw [h2] at h1
  rw [hom_id_to_id φ hp g] at h1
  rw [two_sided_inv (φ (ι g)) (φ g) h1]
  rw [inv_inv_eq_self]
  -- END SAMPLE SOLUTION


/-

You have two options on where to go next. If you're familiar with basic modular arithmetic
(including gcds, lcms, and the Euclidean algorithm), you can go straight to Sheet2. If you would
like a refresher, or simply to see how these concepts are implemented in Lean, feel free to go to
the sheet named `Sheet02.lean`.

-/
