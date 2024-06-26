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

  -- ## INTERNAL: AS THE PROBLEM SETS DEVELOP, CAN ADD MORE PROBLEMS HERE
  -- ## TO CHECK PROFICIENCY IN EACH OF THE CRUCIAL ALGEBRA TACTICS

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
    -- take in arguments as is usual with `cases` and `cases'`.
    example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
      intros h z
      rcases h z with ⟨x, rfl⟩
      use f x
      rfl
      done

    -- Corrollary: bijectivity composition
    example (f : α → β) (g : β → γ) (h1 : Bijective f) (h2 : Bijective g) :
    Bijective (g ∘ f) := by
      cases' h1 with finv hf
      cases' h2 with ginv hg


      sorry


  -- You just proved lots about two injective maps `f, g` and the composition
  -- of those maps `g ∘ f` .
  -- Nice to see all those classic Lean tactics again, right?
  -- Make sure you are fully comfortable with what we've seen above,
  -- including `intros, apply, exact, done`. See `Chapter 0` for a refresher.
  -- They are basic, but before moving on to the next chapter, it is necessary
  -- to be quite familiar with them.
