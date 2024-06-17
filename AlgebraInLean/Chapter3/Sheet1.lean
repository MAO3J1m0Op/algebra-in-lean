import «AlgebraInLean».Basic

namespace Defs

  namespace Subgroups

    -- If G is a group, then a subgroup of G is a subset of G that is itself a
    -- group under G's group operation. We encode a subgroup as a Lean
    -- structure, notably not as a type class, as we wish to represent subgroups
    -- merely as subsets with additional properties.
    structure Subgroup (G : Type*) [Group G] where
      -- We represent the subgroup's corresponding set using Mathlib's `Set`
      -- type. Upon viewing the Mathlib documentation for the set (if you are
      -- viewing this file in Visual Studio Code, you may Ctrl-Click on the
      -- keyword to consult its definiton), we see that it is merely a wrapper
      -- for `G → Prop`, meaning it is a function that determines what is and
      -- is not in the set.
      carrier : Set G
      -- This proposition asserts that the group is nonempty, namely that the
      -- subgroup contains the identity of G.
      nonempty : 𝕖 ∈ carrier
      -- The below propositions assert that the subgroup is closed under the
      -- group operation μ and the inverse function ι.
      mul_closure : ∀ a b, a ∈ carrier → b ∈ carrier → μ a b ∈ carrier
      inv_closure : ∀ a : G, a ∈ carrier → ι a ∈ carrier

    -- This instance coerces `Subgroup G` to `Set G`.
    instance [Group G] : Coe (Subgroup G) (Set G) := ⟨λ H ↦ H.carrier⟩
    -- This instance permits the use of `H : Subgroup G`. An element `a : H`,
    -- will have two properties: `a.val`, which is of type `G`, and
    -- `a.property`, which is the hypothesis that `a.val ∈ H`.
    instance {G : Type u} [Group G] : CoeSort (Subgroup G) (Type u) := ⟨λ H ↦ H.carrier⟩
    -- For more information on coercions, consult the link below.
    -- https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html

    -- More notation! This allows us to use the element-of symbol (∈) for subgroups.
    instance {G : Type*} [Group G] : Membership G (Subgroup G) :=
      ⟨λ g H ↦ g ∈ H.carrier⟩

    -- The instances above allow us to assert that `H : Subgroup G` is itself a
    -- group. We do this by implementing our `Group` interface on all `H`. As
    -- you complete the proofs yourself, you will notice that many of the
    -- properties are inherited from the parent group's structure, so the mere
    -- assertion of closure of H under μ and ι are sufficient to prove that H is
    -- a group!
    instance [Group G] {H : Subgroup G} : Group H where
      -- Our operation now needs to be of type H → H → H instead of G → G → G.
      -- The ⟨ ⟩ notation divides the subgroup elements into its two properties.
      op := λ ⟨a, ha⟩ ⟨b, hb⟩ ↦ by
        have μ_closed : μ a b ∈ H
        -- SOLUTION
        · exact H.mul_closure a b ha hb

        -- Create an element of H from G, again using ⟨ ⟩ notation.
        exact ⟨μ a b, μ_closed⟩

      op_assoc := by
        -- Hint: you can use ⟨ ⟩ notation in `intro` as well!
        intro a b c
        ext
        apply op_assoc

      -- Make sure to provide both an element e : G and a proof that e ∈ H.
      id := ⟨𝕖, H.nonempty⟩

      -- Recall that the next two fields are proofs. If you ever forget the type
      -- signature of a structure field, you may either scroll to consult the
      -- definition, or alternatively, if one is viewing this document in Visual
      -- Studio Code, one may hover over the name of the field.
      id_op := by
        intro a
        ext
        apply id_op

      op_id := by
        intro a
        ext
        apply op_id

      -- Similarly to what we did above for `op`, we must show that `inv` is
      -- also closed.
      inv := λ ⟨a, ha⟩ ↦ by

        have ι_closed : ι a ∈ H
        -- SOLUTION
        · exact H.inv_closure a ha

        exact ⟨ι a, ι_closed⟩

      inv_op := by
        intro a
        ext
        apply inv_op

    -- The largest possible subgroup of G contains every element of G.
    def Complete [Group G] : Subgroup G where
      carrier := Set.univ

      -- Try to come up with one-line solutions for each of the below proofs
      -- PROOFS BELOW ARE SOLUTIONS
      nonempty := by
        exact trivial

      mul_closure := by
        exact λ a b ha hb ↦ trivial

      inv_closure := by
        exact λ a ha ↦ trivial

    -- The smallest possible subgroup of G is called _trivial_ subgroup. What
    -- would this smallest subgroup be?
    def Trivial [Group G] : Subgroup G where
      -- BELOW ARE SOLUTIONS
      carrier := {𝕖}
      nonempty := by
        trivial
      mul_closure := by
        intro a b ha hb
        rw [ha, hb, op_id]
        trivial
      inv_closure := by
        intro a ha
        rw [ha, inv_id]
        trivial

    def Centralizer [Group G] (S : Set G) : Subgroup G where
      -- FIXME : all are written with primitive group axioms. If more robust
      -- ones are provided in ch. 1, we can work to use those instead.
      carrier := {g | ∀ s ∈ S, μ g s = μ s g}
      nonempty := by
        intro s hs
        rw [id_op, op_id]
      mul_closure := by
        intro a b ha hb s hs
        rw [op_assoc, hb, ←op_assoc, ha, op_assoc] <;> exact hs
      inv_closure := by
        -- Nasty, but works
        intro a ha s hs
        symm
        rw [←op_id s, ←op_inv a]
        repeat rw [←op_assoc]
        apply congr <;> try rfl
        rw [op_assoc, op_inv, op_id]
        nth_rw 1 [←id_op s]
        rw [←inv_op a]
        repeat rw [op_assoc]
        apply congr <;> try rfl
        apply congr <;> try rfl
        exact ha s hs

    def conjugate [Group G] (n g : G) : G := μ (μ n g) (ι g)

    def Normalizer [Group G] (S : Set G) : Subgroup G where
      carrier := {g | ∀ s ∈ S, μ (μ g s) (ι g) = s}
      nonempty := by
        intro s hs
        rw [id_op, inv_id, op_id]
      mul_closure := by
        intro a b ha hb s hs
        rw [inv_anticomm]
        rw [op_assoc, op_assoc a, ←op_assoc s, ←op_assoc b, ←op_assoc b]
        rw [hb s hs, ←op_assoc, ha s hs]
      inv_closure := by
        intro a ha b hb
        have inv_inv_eq_self : ∀ g : G, ι (ι g) = g := by
          intro x
          have h1 : ∀ g : G, μ (ι (ι g)) (ι g) = 𝕖 := by
            intro y
            rw[inv_op]
          have h2 : ∀ g : G, μ (g) (ι g) = 𝕖 := by
            intro z
            rw[op_inv] --ONLY VALID WITH op_inv PROOF
          have h1_x := h1 x
          have h2_x := h2 x
          rw [← h2_x] at h1_x
          sorry -- FIXME do we have a uniqe inverse theorem?
        have h3_a := inv_inv_eq_self a
        rw [h3_a]
        have h3 : μ (μ a b) (ι a) = b → μ (μ (ι a) b) a = b := by
          intro ht
          have hp : μ (μ a b) (ι a) = b → μ (ι a) (μ (μ a b) (ι a)) = μ (ι a) b := by
            intro hu
            rw [hu]
          apply hp at ht
          rw [op_assoc, ← op_assoc, inv_op, id_op] at ht
          have hq : μ b (ι a) = μ (ι a) b → μ (μ b (ι a)) a = μ (μ (ι a) b) a := by
            intro hu
            rw [hu]
          apply hq at ht
          rw [op_assoc, inv_op, op_id] at ht
          symm
          exact ht
        rw [h3]
        have ha_b := ha b
        apply ha_b at hb
        exact hb

    variable {G : Type*} [Group G]

    -- We define a subgroup to be _normal_ if the subgroup is closed under
    -- conjugation with any element of G.
    -- TODO: include conjugation in the definition?
    def normal [Group G] (H : Subgroup G) : Prop :=
      ∀ g h : G, h ∈ H → μ (μ g h) (ι g) = h

    theorem foldml_append [Monoid M] (xs ys : List M)
        : List.foldl μ 𝕖 (xs ++ ys) = μ (List.foldl μ 𝕖 xs) (List.foldl μ 𝕖 ys) := by
      sorry

    def Generate (S : Set G) : Subgroup G where
      carrier := {g | ∃ xs : List {s : G // s ∈ S ∨ ι s ∈ S}, List.foldl μ (𝕖 : G) xs = g}
      nonempty := Exists.intro [] rfl
      mul_closure := by
        dsimp at *
        intro a b ⟨as, has⟩ ⟨bs, hbs⟩
        use as ++ bs
        sorry
      inv_closure :=
      sorry

    def Homomorphism [Group G] [Group H] (φ : G → H) : Prop := ∀ a b : G, μ (φ a) (φ b) = φ (μ a b)

    def Kernel [Group G] [Group H] (φ : G → H) (h : Homomorphism φ) : Subgroup G where
      carrier := {g | φ g = 𝕖}
      nonempty := sorry
      mul_closure := sorry
      inv_closure := sorry

  end Subgroups

end Defs
