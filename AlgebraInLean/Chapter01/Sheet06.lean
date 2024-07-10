import AlgebraInLean.Chapter01.Sheet05

namespace AlgebraInLean

/-
## Challenge Sheet

The next example of groups we will go over are the dihedral groups Dₙ. Similarly to the cyclic
groups, the dihedral groups also represent symmetries on a regular n-gon. However, Dₙ includes both
rotations and reflections. Feel free to skip this section and come back to it at a later time if the
content is overwhelming.
-/

/--
The dihedral group Dₙ has 2n elements: the n rotations already in Cₙ, and the reflections of all
of these rotations (reflection first, then rotation).
-/
inductive Dihedral (n : ℕ) [NeZero n] : Type
| rotation : Fin n → Dihedral n
| reflection : Fin n → Dihedral n

variable {n : ℕ} [NeZero n]

def Dihedral.op : (Dihedral n) → (Dihedral n) → (Dihedral n)
| .rotation n, .rotation m => .rotation (μ n m)
| .rotation n, .reflection m => .reflection (μ n m)
| .reflection n, .rotation m => .reflection (μ n (ι m))
| .reflection n, .reflection m => .rotation (μ n (ι m))

def Dihedral.inv : (Dihedral n) → (Dihedral n)
| .rotation n => .rotation (ι n)
| .reflection n => .reflection n

instance (n : ℕ) [NeZero n] : Group (Dihedral n) where
  op := Dihedral.op

  -- These proofs are pretty tricky, so here's one example
  op_assoc a b c := by
    cases a
    all_goals cases b
    all_goals cases c
    all_goals simp only [μ]
    all_goals simp only [Dihedral.op, op_assoc, inv_anticomm, inv_inv]
    all_goals rw [op_comm (ι _)]
    done

  id := .rotation 𝕖

  op_id a := by
    -- sorry
    -- SAMPLE SOLUTION
    cases a
    all_goals simp only [μ]
    all_goals simp only [Dihedral.op, inv_id, op_id]
    done
    -- END OF SAMPLE SOLUTION

  id_op a := by
    -- sorry
    -- SAMPLE SOLUTION
    cases a
    all_goals simp only [μ]
    all_goals simp only [Dihedral.op, id_op]
    done
    -- END OF SAMPLE SOLUTION

  inv := Dihedral.inv

  inv_op a := by
    -- sorry
    -- SAMPLE SOLUTION
    cases a
    all_goals simp only [μ]
    all_goals simp only [Dihedral.op, Dihedral.inv, inv_op, op_inv]
    all_goals rfl
    done
    -- END OF SAMPLE SOLUTION

/-
Dₙ is the first example we've seen of a non-abelian group. In fact, D₃ is the smallest non-abelian
group.
-/
theorem D₃_nonabelian : ¬(∀ (a b : Dihedral 3), μ a b = μ b a) := by
  -- sorry
  -- SAMPLE SOLUTION
  intro h
  let a : Dihedral 3 := .rotation 1
  let b : Dihedral 3 := .reflection 0
  specialize h a b
  simp [μ, Magma.op, Dihedral.op, a, b, ι, Group.inv, Fin.add] at h
  done
  -- END OF SAMPLE SOLUTION
