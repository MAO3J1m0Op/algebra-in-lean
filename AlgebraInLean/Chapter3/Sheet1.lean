import «AlgebraInLean».Basic

namespace Defs

  namespace Subgroups

    -- If G is a group, then a subgroup H of G is a subset of G that is itself
    -- a group under G's group operation satisfying three properties.
    -- 1. The identity in G is the identity in H (H is therefore nonempty)
    -- 2. ∀ a, b ∈ H then μ a b ∈ H
    -- 3. ∀ a ∈ H, then ι a ∈ H
    -- Subgroups are denoted by the less than or equal sign, so we write H ≤ G.
    -- We encode a subgroup as a Lean structure, notably not as a type class
    -- to emphasize that subgroups are simply subsets of groups satisfying
    -- specific properties.
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

    -- This notation allows us to use the element-of symbol (∈) for subgroups.
    instance {G : Type*} [Group G] : Membership G (Subgroup G) :=
      ⟨λ g H ↦ g ∈ H.carrier⟩

    -- The instances above allow us to assert that `H : Subgroup G` is itself a
    -- group. We do this by implementing our `Group` interface on all `H`. As
    -- you complete the proofs yourself, you will notice that many of the
    -- properties are inherited from the parent group's structure, so the mere
    -- assertion of closure of H under μ and ι are sufficient to prove that H
    -- is a group!
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

    -- The largest possible subgroup of G contains every element of G. We
    -- call this subgroup as `Maximal`, and it represents the specific case
    -- H ≤ G where H = G.
    def Maximal [Group G] : Subgroup G where
      carrier := Set.univ

      -- Try to come up with one-line solutions for each of the below proofs
      -- PROOFS BELOW ARE SOLUTIONS
      nonempty := by
        exact trivial

      mul_closure := by
        exact λ a b ha hb ↦ trivial

      inv_closure := by
        exact λ a ha ↦ trivial

    -- The smallest possible subgroup of G is called the _trivial_ subgroup.
    -- What would this smallest subgroup be?
    -- To avoid confusion with the already defined `trivial` in Lean, we will
    -- call this `Minimal`.
    def Minimal [Group G] : Subgroup G where
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

    -- We have defined a subgroup to be a subset of a group closed under
    -- operation and three additional properties. However, to show H is a
    -- subgroup of G it suffices to show two things:
    -- 1. H ≠ {∅}
    -- 2. for all x, y ∈ H, μ x (ι y) ∈ H
    -- That is, a subset H of G is a subgroup IFF the two properties above
    -- hold, this is known as the Subgroup Criterion.
    -- Notice that the language nonempty we used to define a subset earlier may
    -- be slightly misleading. Earlier, we asserted nonempty by claiming the
    -- identity existed in the subset. However, this criterion truly only
    -- requires the subset to be nonempty-then the second condition can be used
    -- to show that the identity must be in the subgroup. The proof is
    -- outlined below and each thing to show (nonempty, inv_closure,
    -- mul_closure) follows from the last.
    def subgroup_criterion [Group G] (S : Set G) (he : ∃ s : G, s ∈ S) (hc : ∀ x y, x ∈ S → y ∈ S → (μ x (ι y)) ∈ S) : Subgroup G where
      carrier := S
      nonempty := by
        obtain ⟨s, hs⟩ := he
        rw [← op_inv s]
        apply hc <;> exact hs
      inv_closure := by
        intro a
        have hc2 := hc
        specialize hc2 𝕖 a
        rw [← id_op (ι a)]
        apply hc2
        have h1 : 𝕖 ∈ S := by
          obtain ⟨s, hs⟩ := he
          rw [← op_inv s]
          apply hc <;> exact hs
        exact h1
      mul_closure := by
        intro a b ha hb
        have hc3 := hc
        have hc4 := hc
        specialize hc3 a (ι b)
        have ht : ι (ι b) = b := sorry -- FIXME use inverse of inverse equals self
        rw [ht] at hc3
        have hf : b ∈ S → ι b ∈ S := by
          intro hb
          rw [← id_op (ι b)]
          specialize hc4 𝕖 b
          apply hc4
          have h1 : 𝕖 ∈ S := by
            obtain ⟨s, hs⟩ := he
            rw [← op_inv s]
            apply hc <;> exact hs
          exact h1
          exact hb
        apply hf at hb
        apply hc3 at ha
        apply ha at hb
        exact hb

    -- An important property of subroups is that for any group G with subgroup
    -- H, and K a subgroup of H (note this works since H itself is a group)
    -- then it must be that K is a subgroup of G. That is, transitivity for
    -- subgroups holds and K ≤ H ≤ G → K ≤ G.
    def subgroup_trans [Group G] (H : Subgroup G) (K : Subgroup H) : Subgroup G where
      carrier := {g : G | ∃ h : H, h ∈ K.carrier ∧ g = h}
      nonempty := by
        use (𝕖 : H)
        constructor
        · exact K.nonempty
        · rfl
      mul_closure := by
        intros x y hx hy
        obtain ⟨hx, hxK, x_eq⟩ := hx
        obtain ⟨hy, hyK, y_eq⟩ := hy
        use (μ hx hy : H)
        constructor
        · exact K.mul_closure hx hy hxK hyK
        · rw [x_eq, y_eq]
          rfl
      inv_closure := by
        intros x hx
        obtain ⟨hx, hxK, xhx⟩ := hx
        use (ι (hx) : H)
        constructor
        · exact K.inv_closure hx hxK
        · rw [xhx]
          rfl

    -- An extension of this transitivity that may be useful is considering
    -- three subgroups K, J, L of G. It follows that if K ≤ J and J ≤ L then
    -- K ≤ L. Try proving this one yourself.
    theorem sgp_trans [Group G] (J K L : Subgroup G) (kj : K.carrier ⊆ J.carrier) (jl : J.carrier ⊆ L.carrier) : K.carrier ⊆ L.carrier := by
      --EXERCISE
      intros x hx
      apply jl
      apply kj
      exact hx

    -- Subgroups also hold under intersection. That is, given two subroups H
    -- and K of a group G, H ∩ K is also a subgroup of G. Let's prove it.
    def subgroup_intersection [Group G] {H K : Set G} (hH : Subgroup G) (hK : Subgroup G) (hHset : H = hH.carrier) (hKset : K = hK.carrier) : Subgroup G where
      --EXERCISE
      carrier := H ∩ K
      nonempty := by
        simp [hHset, hKset]
        exact ⟨hH.nonempty, hK.nonempty⟩
      mul_closure := by
        intro a b ha hb
        simp [hHset, hKset] at *
        exact ⟨hH.mul_closure a b ha.left hb.left, hK.mul_closure a b ha.right hb.right⟩
      inv_closure := by
        intros a ha
        simp [hHset, hKset] at *
        exact ⟨hH.inv_closure a ha.left, hK.inv_closure a ha.right⟩

    -- So far we have explicitly defined a group G in each definition and
    -- theorem for clarity, but we could simply define G as a group for any
    -- subsequent theorems and definitions. From here on out, any instance of G
    -- will be assumed to be a group.
    variable {G : Type*} [Group G]

    -- Given a group G and a subset of that group, S, the subgroup generated
    -- by S is the smallest order subgroup H ≤ G such that S ⊆ H. We show that
    -- such a subset H which contains S is a subgroup in the example below.
    def Generate (S : Set G) : Subgroup G where
      carrier := {g : G | ∀ H : Subgroup G, S ⊆ H → g ∈ H}
      nonempty := by
        intro H _
        exact H.nonempty
      mul_closure := by
        dsimp at *
        intro a b ha hb H hH
        apply H.mul_closure
        · exact ha H hH
        · exact hb H hH
      inv_closure := by
        intro a ha H hH
        apply H.inv_closure
        exact ha H hH

  end Subgroups

end Defs
