import AlgebraInLean.World01.Sheet5

namespace AlgebraInLean

/- The next example of a group we will go over is the dihedral group, Dn. Similarly to the cyclic
group, Dn is a group of the symmetries of a regular n-gon. However, in the dihedral group, both
rotations and reflections are allowed. The group action is again composition of these symmetries. -/

/- Dn has 2n elements: the n rotations already in Cn, and all of these rotations after rotating
around a vertical line. This means that we can represent Dn as an ordered pair, with a boolean
representing whether or not this element is a reflection, and a natural number less than n
representing which spot the first vertex gets sent to. -/
def Dn (n : ℕ) : Type := Bool × (Fin n)

/- Both these functions are used as helper functions in the Dn_op function. -/
/- f_no_ref describes composing a rotation by another element in Dn. Due to how function composition
works, this other element happens first. This means that applying a pure rotation after any other
element preserves whether or not the element is a reflection, and adds the new rotation to how much
the other element rotated the polygon. This is done with an if-then-else block, which allows you to
return different values depending on if you have a rotation or reflection. -/
/- f_ref is similar, except it describes composing a reflection with another element. This time,
whether the element is a reflection or not is switched, since composing two reflections gives a
rotation, and composing a reflection and a rotation returns a reflection. Now, the two rotations are
subtracted, since the reflection switches which direction of the rotation of the first element. -/
def f_no_ref (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x y => if (y.1 = true) then {1 := true, 2 := Fin.add x.2 y.2} else {1 := false, 2 := Fin.add x.2 y.2}

def f_ref (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x y => if (y.1 = true) then {1 := false, 2 := Fin.sub x.2 y.2} else {1 := true, 2 := Fin.sub x.2 y.2}

/- Dn_op composes any two elements by using another if-then-else block to decide
which helper function to use. -/
def Dn_op (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x => if (x.1 = true) then (f_ref n x) else (f_no_ref n x)

/- Dn_inv is the inverse function. By looking at how Dn_op is defined, try to understand
why the inverse is defined this way. -/
def Dn_inv (n : ℕ) : (Dn n) → (Dn n) := fun x => if (x.1 = true) then {1 := true, 2 := x.2} else {1 := false, 2 := -x.2}

/- The following four theorems are restatements of the definitions above, which makes
it easier to write proofs. -/
theorem h_def_inv : Dn_inv n x =  if (x.1 = true) then {1 := true, 2 := x.2} else {1 := false, 2 := -x.2} := rfl

theorem h_def_op : Dn_op n = (fun x => if (x.1 = true) then (f_ref n x) else (f_no_ref n x)) := rfl

theorem h_def_ref : f_ref n x = fun y => if (y.1 = true) then {1 := false, 2 := Fin.sub x.2 y.2} else {1 := true, 2 := Fin.sub x.2 y.2} := rfl

theorem h_def_no_ref : f_no_ref n x = fun y => if (y.1 = true) then {1 := true, 2 := Fin.add x.2 y.2} else {1 := false, 2 := Fin.add x.2 y.2} := rfl

/- The following eight theorems are ways to unfold the if-then-else blocks. Each one
takes a statement about whether an element is a rotation or reflection, then returns
a proof that gives the more specific value of one of the functions.-/
theorem h_inv_t {x : Dn n} : x.1 = true → (Dn_inv n x = {1 := true, 2 := x.2}) := by
  intro h
  rw [h_def_inv]
  exact if_pos h

theorem h_inv_f {x : Dn n} : x.1 = false → (Dn_inv n x = {1 := false, 2 := -x.2}) := by
  intro h
  rw [h_def_inv]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2

theorem h_op_t {x : Dn n} : x.1 = true → (Dn_op n x = f_ref n x) := by
  intro h
  rw [h_def_op]
  exact if_pos h

theorem h_op_f {x : Dn n} : x.1 = false → (Dn_op n x = f_no_ref n x) := by
  intro h
  rw [h_def_op]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2

theorem h_ref_t {x y : Dn n} : y.1 = true → (f_ref n x y = {1 := false, 2 := Fin.sub x.2 y.2}) := by
  intro h
  rw [h_def_ref]
  exact if_pos h

theorem h_no_ref_t {x y : Dn n}: y.1 = true → (f_no_ref n x y= {1 := true, 2 := Fin.add x.2 y.2}) := by
  intro h
  rw [h_def_no_ref]
  exact if_pos h

theorem h_no_ref_f {x y : Dn n}: y.1 = false → (f_no_ref n x y= {1 := false, 2 := Fin.add x.2 y.2}) := by
  intro h
  rw [h_def_no_ref]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2

theorem h_ref_f {x y : Dn n}: y.1 = false → (f_ref n x y= {1 := true, 2 := Fin.sub x.2 y.2}) := by
  intro h
  rw [h_def_ref]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2

/- Finally, we can claim that Dn is a group. -/
instance (n : ℕ) (hpos : NeZero n) : Group (Dn n) where
  op := Dn_op n

  /- The proof that the group operation is associative requires splitting the theorem into eight
  cases, depending on which elements are rotations or reflections. For each case, we then used the
  theorems above to simplify both sides of the equation into exact values. Each case then becomes a
  simple property of the naturals, such as a-(b+c)=a-b-c. You don't have to prove anything here, but
  read and understand how the proof is written. -/
  op_assoc := by
    have h_exact : ∀ a b c : Dn n, Dn_op n (Dn_op n a b) c = Dn_op n a (Dn_op n b c)
    intro a b c
    have h : a.1 = true ∨ a.1 = false
    exact Bool.eq_false_or_eq_true a.1
    cases h with
    | inl hat =>
      have h : b.1 = true ∨ b.1 = false
      exact Bool.eq_false_or_eq_true b.1
      cases h with
      | inl hbt =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw [h_op_t hat, h_ref_t hbt]
          have hfr : (false, a.2.sub b.2).1 = false := rfl
          rw [h_op_f hfr, h_no_ref_t hct, h_op_t hbt, h_ref_t hct]
          have hfl : (false, b.2.sub c.2).1 = false := rfl
          rw [h_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).add c.2 = a.2.sub (b.2.sub c.2)
          exact fun a b c => sub_add a.2 b.2 c.2
          specialize h a b c
          rw [h]
        | inr hcf =>
          rw [h_op_t hat, h_ref_t hbt]
          have hfr : (false, a.2.sub b.2).1 = false := rfl
          rw [h_op_f hfr, h_no_ref_f hcf, h_op_t hbt, h_ref_f hcf]
          have htl : (true, b.2.sub c.2).1 = true := rfl
          rw [h_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).add c.2 = a.2.sub (b.2.sub c.2)
          exact fun a b c => sub_add a.2 b.2 c.2
          specialize h a b c
          rw [h]
      | inr hbf =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw [h_op_t hat, h_ref_f hbf]
          have htr : (true, a.2.sub b.2).1 = true := rfl
          rw [h_op_t htr, h_ref_t hct, h_op_f hbf, h_no_ref_t hct]
          have htl : (true, b.2.add c.2).1 = true := rfl
          rw [h_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).sub c.2 = a.2.sub (b.2.add c.2)
          exact fun a b c => sub_sub a.2 b.2 c.2
          specialize h a b c
          rw [h]
        | inr hcf =>
          rw [h_op_t hat, h_ref_f hbf]
          have htr : (true, a.2.sub b.2).1 = true := rfl
          rw [h_op_t htr, h_ref_f hcf, h_op_f hbf, h_no_ref_f hcf]
          have hfl : (false, b.2.add c.2).1 = false := rfl
          rw [h_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).sub c.2 = a.2.sub (b.2.add c.2)
          exact fun a b c => sub_sub a.2 b.2 c.2
          specialize h a b c
          rw [h]
    | inr haf =>
      have h : b.1 = true ∨ b.1 = false
      exact Bool.eq_false_or_eq_true b.1
      cases h with
      | inl hbt =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw [h_op_f haf, h_no_ref_t hbt]
          have htr : (true, a.2.add b.2).1 = true := rfl
          rw [h_op_t htr, h_ref_t hct, h_op_t hbt, h_ref_t hct]
          have hfl : (false, b.2.sub c.2).1 = false := rfl
          rw [h_no_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).sub c.2 = a.2.add (b.2.sub c.2)
          exact fun a b c => add_sub_assoc a.2 b.2 c.2
          specialize h a b c
          rw [h]
        | inr hcf =>
          rw [h_op_f haf, h_no_ref_t hbt]
          have htr : (true, a.2.add b.2).1 = true := rfl
          rw [h_op_t htr, h_ref_f hcf, h_op_t hbt, h_ref_f hcf]
          have htl : (true, b.2.sub c.2).1 = true := rfl
          rw [h_no_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).sub c.2 = a.2.add (b.2.sub c.2)
          exact fun a b c => add_sub_assoc a.2 b.2 c.2
          specialize h a b c
          rw [h]
      | inr hbf =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw [h_op_f haf, h_no_ref_f hbf]
          have hfr : (false, a.2.add b.2).1 = false := rfl
          rw [h_op_f hfr, h_no_ref_t hct, h_op_f hbf, h_no_ref_t hct]
          have htl : (true, b.2.add c.2).1 = true := rfl
          rw [h_no_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).add c.2 = a.2.add (b.2.add c.2)
          exact fun a b c => add_assoc a.2 b.2 c.2
          specialize h a b c
          rw [h]
        | inr hcf =>
          rw [h_op_f haf, h_no_ref_f hbf]
          have hfr : (false, a.2.add b.2).1 = false := rfl
          rw [h_op_f hfr, h_no_ref_f hcf, h_op_f hbf, h_no_ref_f hcf]
          have hfl : (false, b.2.add c.2).1 = false := rfl
          rw [h_no_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).add c.2 = a.2.add (b.2.add c.2)
          exact fun a b c => add_assoc a.2 b.2 c.2
          specialize h a b c
          rw [h]
    exact fun a => h_exact a

  /- The identity of Dn is the element that does not rotate or reflect the polygon. -/
  id := {1 := false, 2:= 0}

  /- Similarly to the proof of op_assoc, op_id splits into two cases, then applies the theorems
  shown earlier on each case to simplify, before lastly showing that the goal is a theorem already
  known about the natural numbers. -/
  op_id := by
    have h : ∀ a : Dn n, (Dn_op n) a (false, 0) = a
    intro a
    have htf := Bool.eq_false_or_eq_true a.1
    cases htf with
    | inl ht =>
      rw [h_op_t ht]
      have hf2 : (false, 0).1 = false := rfl
      rw [h_ref_f hf2]
      simp
      have hzero : a.2.sub 0 = a.2 := sub_zero a.2
      rw [hzero, ←ht]
      rfl
    | inr hf =>
      rw [h_op_f hf]
      have hf2 : (false, 0).1 = false := rfl
      rw [h_no_ref_f hf2]
      simp
      have hzero : a.2.add 0 = a.2 := add_zero a.2
      rw [hzero, ←hf]
      rfl
    exact fun a => h a

  /- id_op is shown in the same way as op_id. -/
  id_op := by
    have h : ∀ a : Dn n, (Dn_op n) (false, 0) a = a
    intro a
    have hf : (false, 0).1 = false := rfl
    rw [h_op_f hf]
    have htf := Bool.eq_false_or_eq_true a.1
    cases htf with
    | inl ht =>
      rw [h_no_ref_t ht]
      simp
      have hzero1 : Fin.add 0 a.2 = 0 + a.2 := rfl
      have hzero2 : 0 + a.2 = a.2 := zero_add a.2
      rw [hzero1, hzero2, ←ht]
      rfl
    | inr hf =>
      rw [h_no_ref_f hf]
      simp
      have hzero1 : Fin.add 0 a.2 = 0 + a.2 := rfl
      have hzero2 : 0 + a.2 = a.2 := zero_add a.2
      rw [hzero1, hzero2, ←hf]
      rfl
    exact fun a => h a

  /- The inverse function is the function defined earlier. -/
  inv := Dn_inv n

  /- inv_op is similar to the other proofs: splitting into cases, simplifing, then
  figuring out what property of the natural numbers it is equivalent to. -/
  inv_op := by
    have h : ∀ a : Dn n, (Dn_op n) (Dn_inv n a) a = (false, 0)
    intro a
    have htf := Bool.eq_false_or_eq_true a.1
    cases htf with
    | inl ht =>
      rw [h_inv_t ht]
      have ht2 : (true, a.2).1 = true := rfl
      rw [h_op_t ht2, h_ref_t ht]
      simp
      have hinv1 : a.2.sub a.2 = a.2 - a.2 := rfl
      have hinv2 : a.2 - a.2 = 0 := sub_eq_zero_of_eq rfl
      rw [hinv1, hinv2]
    | inr hf =>
      rw [h_inv_f hf]
      have hf2 : (false, -a.2).1 = false := rfl
      rw [h_op_f hf2, h_no_ref_f hf]
      simp
      have hinv1 : (-a.2).add a.2 = (-a.2) + a.2 := rfl
      have hinv2 : (-a.2) + a.2 = 0
      exact neg_add_self a.2
      rw [hinv1, hinv2]
    exact fun a => h a

/- Dn is the first example we've seen of a non-abelian group. In fact, D3 is the smallest
non-abelian group. -/

/- First, we have to claim that D3 is a group. This is simple, since we just proved it. -/
instance : Group (Dn 3) := instGroupDnOfNeZeroNat 3 NeZero.succ

/- Now, try to find a counterexample and show that D3 cannot be abelian-/
theorem D3_nonabelian : ¬(∀ a b : (Dn 3), μ a b = μ b a) := by
  -- sorry
  -- SAMPLE SOLUTION
  intro h
  let a : Dn 3 := (false, 1)
  let b : Dn 3 := (true, 0)
  specialize h a b
  have h2 : μ a b = (true, 1) := rfl
  have h3 : μ b a = (true, 2) := rfl
  have hne : (μ a b).2 ≠ (μ b a).2
  rw[h2, h3]
  simp
  apply hne
  rw[h]
  -- END OF SAMPLE SOLUTION
