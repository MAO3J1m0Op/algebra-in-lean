import AlgebraInLean.Chapter02.Sheet03

set_option linter.unusedTactic false

namespace AlgebraInLean

/-
Another special structure of morphism is the endomorphism, which is a morphism from an object to
itself. As with other kinds of morphisms, the relevant structure is omitted when it can be inferred
from context. Another kind of endomorphism you are accustomed to are square matrices in linear
algebra (when interpreted as linear maps), which are vector space endomorphisms.

From endomorphisms arises our final definition: the automorphism. An automorphism is a endomorphism
that is also an isomorphism. We have already seen an example of this in the identity function, but
there are more interesting options. You can think of automorphisms like a permutation of the
elements of a group that preserves the group structure.

Rather than defining these separately from `Homomorphism` in Lean, whether or not a particular
homomorphism is an endomorphism can be directly determined from its type signature: merely check
whether the domain and codomain are the same.
-/

variable {G : Type*}

/-
One important automorphism is the inverse, but this is only an automorphism for abelian groups.

Hint: see `inv_anticomm`
-/
/-- -/
theorem Group.inv_automorphism [AbelianGroup G] : Isomorphism (ι : G → G) := by
  -- SAMPLE SOLUTION
  constructor
  · intro a b
    rw [inv_anticomm, op_comm]
  · exact inv_bijective
  -- END SAMPLE SOLUTION
  done

instance [Group G] (h : Group.Isomorphism (ι : G → G)) : AbelianGroup G where
  op_comm a b := by
    -- SAMPLE SOLUTION
    obtain ⟨h₁, ⟨h₂, _⟩⟩ := h
    apply h₂
    rw [←h₁, inv_anticomm]
    -- END SAMPLE SOLUTION
    done

/-
We will now consider another important automorphism called conjugation. For group elements `a` and
`g`, the conjugation of `a` by `g` is the element `g a g⁻¹`. Two elements `a` and `b` are said to be
conjugates if there exists some element `g` such that `b = g a g⁻¹`. This is also an equivalence
relation (like isomorphism), but we will not discuss this now.

You may be familiar with the particular case of invertible n × n matrices (the "general linear
group" GL(n)), where conjugacy is called matrix similarity (recall that two matrices A and B are
similar when there is some matrix C such that B = CAC⁻¹).
-/

variable [Group G]

/-- Conjugation the second argument by the first -/
def Group.conj : G → G → G := λ (g a : G) ↦ μ (μ g a) (ι g)

/-
Like `μ`, `conj` is a "curried" function, meaning that rather than taking in two arguments, it takes
in one argument and returns another function that takes in the second argument. In Lean's syntax,
this is very convenient to use (`conj g a` is the conjugation of `a` by `g`), and has the benefit
that we can easily do "partial application" where the function only has one argument present and the
other is free to vary. That is, `conj g = λ a ↦ g a g⁻¹`. We claim that this partially-applied
function is an automorphism.

First, here's an easier theorem to get you used to this definition.
-/

/-- Conjugation by the identity element is just the identity function -/
theorem Group.conj_id_eq_id : conj (𝕖 : G) = id := by
  -- SAMPLE SOLUTION
  unfold conj
  ext x -- TODO: explain
  rw [inv_id, id_op, op_id]
  rfl
  -- END SAMPLE SOLUTION
  done

/-- Conjugation by a particular element g is an automorphism -/
theorem Group.conj_automorphism (g : G) : Isomorphism (conj g) := by
  /- Hint: this proof has a lot of rewriting, especially with `op_assoc` -/
  -- SAMPLE SOLUTION
  constructor
  · intro a b
    unfold conj
    rw [ op_assoc g b
       , ←op_assoc _ g
       , op_assoc _ (ι g)
       , inv_op
       , op_id
       , op_assoc
       , op_assoc
       , op_assoc
       ]
  · constructor
    · intro a b h
      have h := right_cancel _ _ _ h
      have h := left_cancel _ _ _ h
      exact h
    · intro b
      use conj (ι g) b
      unfold conj
      rw [ inv_inv
         , op_assoc (ι g)
         , ←op_assoc g
         , op_inv
         , id_op
         , op_assoc
         , op_inv
         , op_id
         ]
  -- END SAMPLE SOLUTION
  done

/-
That proof was tough, but it is very important! Its merits will become more apparent later when
learning about group actions. We finish this off with one last definition which will show its use
later.

****

As we proved before, isomorphism is preserved under function composition and inversion. Thus, if we
consider the automorphisms of a particular group G, it is closed under function composition and
inversion. Thus, it forms a group.

To construct the type of automorphisms, we use Lean's subtypes. For some type `α` and predicate
`p : α → Prop`, `{x : α // p x}` is a `Subtype` containing the elements of `α` that satisfy `p`.
Formally, an object `y` of such a type is built from an object `y.val : α` and a proof
`y.property : p y.val`. This should be reminiscent of `∃`, but the latter represents just the idea
that such an element exists, which specifying which one it is (to extract this element, one needs to
invoke the axiom of choice).
-/

/-- The type of automorphisms of G -/
def Group.Automorphisms (G : Type*) [Group G] : Type _ := {φ : G → G // Isomorphism φ}

@[ext] -- allows the `ext` tactic to use this theorem automatically
theorem Group.Automorphisms.ext {a b : Automorphisms G} : a.val = b.val → a = b := Subtype.ext

noncomputable instance : Group (Group.Automorphisms G) where
  op a b := {
    val := a.val ∘ b.val
    property := by
      -- SAMPLE SOLUTION
      exact Group.isomorphism_comp b.prop a.prop
      -- END SAMPLE SOLUTION
      done
  }

  op_assoc a b c := by
    -- SAMPLE SOLUTION
    rfl
    -- END SAMPLE SOLUTION
    done

  id := {
    val :=
      -- SAMPLE SOLUTION
      id
      -- END SAMPLE SOLUTION
    property := by
      -- SAMPLE SOLUTION
      exact Group.id_isomorphism
      -- END SAMPLE SOLUTION
      done
  }

  op_id a := by
    -- SAMPLE SOLUTION
    rfl
    -- END SAMPLE SOLUTION
    done

  id_op a := by
    -- SAMPLE SOLUTION
    rfl
    -- END SAMPLE SOLUTION
    done

  inv a := {
    val := inv_of_bijective a.prop.right
    property := by
      -- SAMPLE SOLUTION
      exact Group.isomorphism_inv a.prop
      -- END SAMPLE SOLUTION
      done
  }

  inv_op a := by
    -- SAMPLE SOLUTION
    unfold μ
    ext : 1
    simp
    exact (inv_of_bijective_spec a.prop.right).left
    -- END SAMPLE SOLUTION
    done

/-
We could also consider automorphisms of other algebraic structures (or even other categories). In
the most basic case where there are no operations or properties to preserve, we that the
automorphisms are just bijections from a set to itself, which (in the finite case) is just the
symmetric group! This means that group-automorphism group is contained within a symmetric group,
which means that it is a subgroup. The next chapter discusses this relation between groups more
in-depth.
-/
