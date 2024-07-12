import AlgebraInLean.Chapter01.Sheet07

set_option linter.unusedTactic false

/-
Let's take a brief break from Algebra to orient ourselves. We are going to explore injectivity and
surjectivity of functions.

Let's start with some basic definitions (you have likely seen some of these already!)
-/

namespace AlgebraInLean

variable {α β γ : Type*}

/-
Brace yourself for a type theory interlude! In Lean's type theory, which is based on the Calculus of
Constructions, there is an infinite hierarchy of types that contain one another. `Type 0` (or just
`Type`) of type `Type 1`, `Type 1 : Type 2`, and so on. A type can never contain itself; if that
were to happen, we would run into a logical paradox (formally referred to as Girard's Paradox, which
is similar to Russel's Paradox)! We classify types using what are called "universes"; in other
words, a universe is a family of types. The special syntax `Type*` means a type of any universe. For
more information on Lean's type system, see
<https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html>.

You are free to think of the types `α`, `β`, and `γ` as sets.

****

We will now discuss some general properties of functions that are not specific to abstract algebra.
First, we define some terms.
-/

/-- A map is injective (or "one-to-one") when f(x) = f(y) only when x = y -/
def Injective (f : α → β) : Prop := ∀ (x y : α), f x = f y → x = y

/-- A map is surjective (or "onto") when its image is the entire codomain -/
def Surjective (f : α → β) : Prop := ∀ (y : β), ∃ (x : α), f x = y

/-- A map is bijective if it is both injective and surjective -/
def Bijective (f : α → β) : Prop := (Injective f ∧ Surjective f)


/-
The tactic `unfold` is helpful for reminding yourself of what a definition means. Try doing
`unfold Surjective` in this proof.
-/
/-- The composition of surjective functions is surjective -/
theorem surjective_comp {f : α → β} {g : β → γ} (h1 : Surjective f) (h2 : Surjective g)
  : Surjective (g ∘ f) := by
  -- SAMPLE SOLUTION
  unfold Surjective
  intro z
  rw [Surjective] at h2
  specialize h2 z
  obtain ⟨y , hy⟩ := h2
  specialize h1 y
  obtain ⟨x, hx⟩ := h1
  use x
  rw [← hy, ← hx]
  rfl
  -- END SAMPLE SOLUTION
  done

/-
Some tactics (notably `rw` and `simp`) accept an `at` parameter that indicates whether it should
work on a particular hypothesis or goal. These usually also accept `at *`, which means to try to
work on the goal and *all* hypotheses. Try using `rw [Injective] at *` in this proof.
-/
/-- The composition of injective functions is injective -/
theorem injective_comp {f : α → β} {g : β → γ} (h1 : Injective f) (h2 : Injective g)
  : Injective (g ∘ f) := by
  -- SAMPLE SOLUTION
  rw [Injective] at *
  intros a1 a2 h
  apply h1
  apply h2
  exact h
  -- END SAMPLE SOLUTION
  done

/-
Another tactic you can try is `change`, which allows changing the type of the goal (or another
hypothesis) to something that is definitionally equivalent. While `unfold` will always expand the
definition of some particular thing, `change` allows you to "fold" it back, as well as modify
multiple things at once. Try doing `change Injective (g ∘ f) ∧ Surjective (g ∘ f)` in this proof.

Hint: The tactic `constructor` may also be useful here.
-/
/-- The composition of bijective functions is bijective -/
theorem bijective_comp {f : α → β} {g : β → γ} (h1 : Bijective f) (h2 : Bijective g)
  : Bijective (g ∘ f) := by
  -- SAMPLE SOLUTION
  change Injective (g ∘ f) ∧ Surjective (g ∘ f)
  obtain ⟨hf_inj, hf_surj⟩ := h1
  obtain ⟨hg_inj, hg_surj⟩ := h2
  constructor
  · apply injective_comp
    · apply hf_inj
    · apply hg_inj
  · apply surjective_comp
    · apply hf_surj
    · apply hg_surj
  -- END SAMPLE SOLUTION
  done

/-
Hint: A new tactic, `rcases` may be helpful with proving this. Hover over `rcases` to see syntax and
usage. This particular tactic peforms cases recursively and can take in arguments as is the norm
with `cases`.
-/
example {f : α → β} {g : β → γ} : Surjective (g ∘ f) → Surjective g := by
  -- SAMPLE SOLUTION
  intros h z
  rcases h z with ⟨x, rfl⟩
  use f x
  rfl
  -- END SAMPLE SOLUTION
  done

/-

You just proved lots about two injective maps `f, g` and the composition of those maps `g ∘ f`.

Nice to see all those classic Lean tactics again, right? Make sure you are fully comfortable with
the tactics `intros`, `apply`, `exact`, `rw`, `cases`, `specialize`. See `Chapter 0` for a
refresher. These are basic, but before moving on to the next chapter, it is necessary to be quite
familiar with them.

-/

/-
Hint: another new useful tactic is `choose`, which invokes the axiom of choice in Lean. Given a
hypothesis `h : ∀ (x : α), ∃ (y : β), p x y`, `choose f hf using h` makes new objects `f : α → β`
and `hf : ∀ (x : α), p x (f x)`.
-/
/-- Bijective functions are invertible -/
theorem inv_from_bijective {f : α → β} (h : Bijective f)
  : ∃ (g : β → α), g ∘ f = id ∧ f ∘ g = id := by
  -- SAMPLE SOLUTION
  rcases h with ⟨h_inj, h_surj⟩
  choose g hg using h_surj
  use g
  constructor
  all_goals ext x -- TODO: explain?
  all_goals simp
  · apply h_inj
    rw [hg (f x)]
  · exact hg x
  -- END SAMPLE SOLUTION
  done

/-- Invertible functions are bijective -/
theorem bijective_from_inv {f : α → β} (h : ∃ (g : β → α), g ∘ f = id ∧ f ∘ g = id)
  : Bijective f := by
  -- SAMPLE SOLUTION
  obtain ⟨g, ⟨h₁, h₂⟩⟩ := h
  constructor
  · intro x y h
    change id x = id y
    rw [←h₁]
    repeat rw [Function.comp_apply]
    rw [h]
  · intro y
    use g y
    rw [← @Function.comp_apply _ _ _ f, h₂]
    rfl
  -- END SAMPLE SOLUTION
  done

/-- A function is bijective iff it is invertible -/
theorem bijective_iff_inv {f : α → β} : Bijective f ↔ ∃ (g : β → α), g ∘ f = id ∧ f ∘ g = id :=
  ⟨inv_from_bijective, bijective_from_inv⟩

/-
This definition is marked as `noncomputable` because `Exists.choose` invokes the axiom of choice.
Since Lean can't evaluate the axiom of choice in a program (i.e., you can't use `#eval` on it), we
need to explicitly opt-in to using it in definitions by marking them as `noncomputable`.
-/
/-- The inverse of a bijective function -/
noncomputable def inv_of_bijective {f : α → β} (h : Bijective f) : β → α :=
  (inv_from_bijective h).choose

/-- Show that `inv_of_bijective` actually produces an inverse -/
noncomputable def inv_of_bijective_spec {f : α → β} (h : Bijective f)
  : (inv_of_bijective h) ∘ f = id ∧ f ∘ (inv_of_bijective h) = id :=
  (inv_from_bijective h).choose_spec

/-- The inverse of a bijective function is a bijection -/
theorem bijective_inv {f : α → β} (h : Bijective f) : Bijective (inv_of_bijective h) := by
  unfold inv_of_bijective
  have hg := (inv_from_bijective h).choose_spec
  /-
  The tactic `set` here defines `g` as `(inv_from_bijective h).choose` and automatically tries to
  replace all instances of `(inv_from_bijective h).choose` in the goal and context with `g`.
  -/
  set g := (inv_from_bijective h).choose
  /- Try to finish out this proof yourself -/
  -- SAMPLE SOLUTION
  apply bijective_from_inv
  use f
  exact hg.symm
  -- END SAMPLE SOLUTION
  done

/-- The inverse map of a group is bijective -/
theorem Group.inv_bijective {G : Type*} [Group G] : Bijective (ι : G → G) := by
  -- SAMPLE SOLUTION
  constructor
  · intros x y h
    apply op_left_cancel (ι x)
    nth_rw 2 [h]
    rw [inv_op, inv_op]
  · intro y
    use ι y
    exact inv_inv y
  -- END SAMPLE SOLUTION
  done
