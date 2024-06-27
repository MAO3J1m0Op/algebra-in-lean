import «AlgebraInLean».Basic

-- Let's take a brief break from Algebra and make sure we know where we are at
-- and where we are going.
-- We are going to talk formalization of injectivity and surjectivity,
-- and everything that follows from those.

-- Beginning with some basic definitions as a reminder (meaning you have likely
-- seen some of these already!)

namespace Interlude
  section bijectivity

  -- Surjectivity, injectivity, and bijectivity of maps
    def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y
    -- Otherwise known as "one-to-one".

    def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y
    -- Otherwise known as "onto".

    def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)
    -- Of course as follows, a map is bijective
    -- it is both injective and surjective.

  end bijectivity

  -- Now let's take a look at some basic problems involving this bijectivity,
  -- not necessarily problems that involve Algebra, but that will test
  -- all of the tactics you have learned thus far.

    -- This is simply restating the definition, so of course it looks a bit different than
    -- the rest of these problems that follow.

    -- A map is bijective ↔ it is both injective and surjective.
    example {α β : Type} (f : α → β) (h1 : Injective f) (h2 : Surjective f) : Bijective f :=
      ⟨h1, h2⟩

    -- Surjectivity composition
    example {α β γ: Type} (f : α → β) (g : β → γ) (h1: Surjective f) (h2 : Surjective g) :
    Surjective (g ∘ f) := by
      intro z
      rw[Surjective] at h2
      specialize h2 z
      cases' h2 with y hy
      cases' (h1 y) with x hx
      use x
      rw[←hy, ←hx]
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

    -- Working backwards
    -- Tip: A new tactic, `rcases` may be helpful with proving this. Hover over `rcases`
    -- to see syntax and usage. This particular tactic peforms cases recursively and can
    -- take in arguments as is the norm with `cases` and `cases'`.
    example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
      intros h z
      rcases h z with ⟨x, rfl⟩
      use f x
      rfl
      done

    -- Corrollary: bijectivity composition

    -- Obviously, this one can be made easier based on the previous two proofs we just
    -- completed. So, let's turn those into theorems in this same namespace that we can
    -- apply for this particular bijectivitiy example.

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
      cases' h2 with y hy
      cases' h1 y with x hx
      use x
      rw [←hy, ←hx]
      rfl
      done

    -- You may want to read up more about `Add.intro` that works to split a logical `∧`
    -- into its two different parts. That will be helpful as you continue.
    example (f : α → β) (g : β → γ) (h1 : Bijective f) (h2 : Bijective g) :
    Bijective (g ∘ f) := by
      cases' h1 with finv hf
      cases' h2 with ginv hg
      rw[Bijective]
      apply And.intro
      apply injective_comp
      · apply finv
      · apply ginv
      apply surjective_comp
      · apply hf
      · apply hg
      done


    -- In the same spirit, let's turn that bijective composition proof into a theorem,
    -- but now it is your turn to do that. This may help you further understand how
    -- L∃∀N categorizes its different types.

    theorem bijective_comp {α β γ : Type} (f : α → β) (g : β → γ) (h1 : Bijective f)
    (h2 : Bijective g) : Bijective (g ∘ f) := by
      cases' h1 with finv hf
      cases' h2 with ginv hg
      rw[Bijective]
      apply And.intro
      apply injective_comp
      · apply finv
      · apply ginv
      apply surjective_comp
      · apply hf
      · apply hg
      done


  -- You just proved lots about two injective maps `f, g` and the composition
  -- of those maps `g ∘ f` .
  -- Nice to see all those classic L∃∀N tactics again, right?
  -- Make sure you are fully comfortable with what we've seen above,
  -- including `intros, apply, exact, rw, cases, specialize`.
  -- See `Chapter 0` for a refresher. These are basic, but before moving
  -- on to the next chapter, it is necessary to be quite familiar with them.

  -- Another crucial tactic you saw in earlier chapters was `have`. Here is the same theorem
  -- about surjectivity composition that you proved earlier. However, try using the `have`
  -- tactic with this one for practice. We've gotten you started below:
  theorem surjective_comp_have {α β γ : Type} (f : α → β) (g : β → γ) (h1 : Surjective f)
  (h2 : Surjective g) : Surjective (g ∘ f) := by
    intro z
    have h2' := h2 z
    cases' h2' with y hy
    have h1' := h1 y
    cases' h1' with x hx
    use x
    have hy' : g y = z := hy
    have hx' : f x = y := hx
    rw [←hy', ←hx']
    rfl

  -- That's all we have for this refresher! Hopefully you have a grasp on our definitions
  -- of injectivity and surjectivity in Lean because proofs are about to get a bit more
  -- advanced in this chapter and in later chapters!
