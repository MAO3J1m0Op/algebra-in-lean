import Mathlib.Tactic
/-

Let's take a brief break from Algebra and make sure we know where we are at
and where we are going.
We are going to talk formalization of injectivity and surjectivity,
and everything that follows from those.

Beginning with some basic definitions as a reminder (meaning you have likely
seen some of these already!)

-/

namespace Defs

namespace Interlude

    /-

    Brace yourself for a type theory interlude!
    In Lean's type theory, the Calculus of Constructions, there is an
    infinite hierarchy of types that contain one another. Type 0 (or simply
    just "Type" is contained in Type 1, Type 1 is contained in Type 2, and
    so on. A type can never contain itself; if that were to happen, we would
    run into a logical paradox! We classify types using what are called
    "universes"; in other words, a universe is a family of types. For more
    information on Lean's type system, see
    https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html.

    You are free to think of α, β, and γ as sets.

    We have already seen many injective functions. One of them is the
    function which takes any group element to its inverse!

    To do this, we need to prove two intuitive propositions: First, a simple
    group identity. Then, a proof that given a group G and an element g in
    G, the inverse of the inverse of g is g itself. In other words, the
    inverse cancels itself out.

    -/

    /- Surjectivity, injectivity, and bijectivity of maps -/

    def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y
    -- Otherwise known as "one-to-one".

    def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y
    -- Otherwise known as "onto".

    def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)
    -- Of course as follows, a map is bijective
    -- it is both injective and surjective.

    /-

    Now let's take a look at some basic problems about bijective maps that will test
    all of the tactics you have learned thus far.

    -/

    /-- A map is bijective if and only if it is injective and surjective. -/
    example {α β : Type} (f : α → β) (h1 : Injective f) (h2 : Surjective f) : Bijective f :=
      ⟨h1, h2⟩

    -- Surjectivity composition
    example {α β γ : Type} (f : α → β) (g : β → γ) (h1: Surjective f) (h2 : Surjective g) :
    Surjective (g ∘ f) := by
      intro z
      rw[Surjective] at h2
      specialize h2 z
      obtain ⟨y , hy⟩ := h2
      specialize h1 y
      obtain ⟨x, hx⟩ := h1
      use x
      rw[← hy, ← hx]
      rfl
      done

    -- Injectivity composition
    example (f : α → β) (g : β → γ) (h1: Injective f) (h2 : Injective g) :
    Injective (g ∘ f) := by
      intros a1 a2 h
      apply h1
      apply h2
      exact h
      done

    /-

    Working backwards
    Tip: A new tactic, `rcases` may be helpful with proving this. Hover over `rcases`
    to see syntax and usage. This particular tactic peforms cases recursively and can
    take in arguments as is the norm with `cases`.

    -/
    example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
      intros h z
      rcases h z with ⟨x, rfl⟩
      use f x
      rfl
      done

    /-

    Corrollary: bijectivity composition

    Obviously, this one can be made easier based on the previous two proofs we just
    completed. So, let's turn those into theorems in this same namespace that we can
    `apply` them for this next bijectivitiy example.

    -/
    theorem injective_comp {α β γ : Type*} (f : α → β) (g : β → γ) (h1 : Injective f)
    (h2 : Injective g) : Injective (g ∘ f) := by
      intros a1 a2 h
      apply h1
      apply h2
      exact h
      done

    theorem surjective_comp {α β γ : Type} (f : α → β) (g : β → γ) (h1 : Surjective f)
    (h2 : Surjective g) : Surjective (g ∘ f) := by
      intro z
      rw [Surjective] at h2
      specialize h2 z
      obtain ⟨y, hy⟩ := h2
      obtain ⟨x, hx⟩ := h1 y
      use x
      rw [← hy, ← hx]
      rfl

    /-

    You may want to read up more about `Add.intro` that works to split a logical `∧`
    into its two different parts. That will be helpful as you continue.

    -/
    example (f : α → β) (g : β → γ) (h1 : Bijective f) (h2 : Bijective g) :
    Bijective (g ∘ f) := by
      obtain ⟨ finv, hf⟩ := h1
      obtain ⟨ginv, hg⟩ := h2
      rw [Bijective]
      constructor
      · apply injective_comp
        · apply finv
        · apply ginv
      · apply surjective_comp
        · apply hf
        · apply hg
      done


    /-

    In the same spirit, let's turn that bijective composition proof into a theorem,
    but now it is your turn to do that. This may help you further understand how
    L∃∀N categorizes its different types

    -/
    theorem bijective_comp {α β γ : Type} (f : α → β) (g : β → γ) (h1 : Bijective f)
    (h2 : Bijective g) : Bijective (g ∘ f) := by
      obtain ⟨finv, hf⟩ := h1
      obtain ⟨ginv, hg⟩ := h2
      rw [Bijective]
      constructor
      · apply injective_comp
        · apply finv
        · apply ginv
      · apply surjective_comp
        · apply hf
        · apply hg
      done


  /-

  You just proved lots about two injective maps `f, g` and the composition
  of those maps `g ∘ f` .
  Nice to see all those classic L∃∀N tactics again, right?
  Make sure you are fully comfortable with what we've seen above,
  including `intros, apply, exact, rw, cases, specialize`.
  See `Chapter 0` for a refresher. These are basic, but before moving
  on to the next chapter, it is necessary to be quite familiar with them.

  Another crucial tactic you saw in earlier chapters was `have`. Here is the same theorem
  about surjectivity composition that you proved earlier. However, try using the `have`
  tactic with this one for practice. We've gotten you started below:

  -/
  theorem surjective_comp_have {α β γ : Type} (f : α → β) (g : β → γ) (h1 : Surjective f)
  (h2 : Surjective g) : Surjective (g ∘ f) := by
    intro z
    have h3 := h2 z
    obtain ⟨y, hy⟩ := h3
    have h4 := h1 y
    obtain ⟨x, hx⟩ := h4
    use x
    rw [← hy, ← hx]
    rfl

  /-

   That's all we 'have' for this refresher! Hopefully you have a grasp on our definitions
   of injectivity and surjectivity in Lean because proofs are about to get a bit more
   advanced in this chapter and in later chapters

  ## GOOD LUCK!!

  -/
