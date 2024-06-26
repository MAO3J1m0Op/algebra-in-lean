import AlgebraInLean.World01.Sheet5
open Defs

def Dn (n : ℕ) : Type := Bool × (Fin n)

def refs (n : ℕ): Set (Dn n) := {x | x.1 = true}

def f_no_ref (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x y => if (y.1 = true) then {1 := true, 2 := Fin.add x.2 y.2} else {1 := false, 2 := Fin.add x.2 y.2}

def f_ref (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x y => if (y.1 = true) then {1 := false, 2 := Fin.sub x.2 y.2} else {1 := true, 2 := Fin.sub x.2 y.2}

def Dn_op (n : ℕ): (Dn n) → (Dn n) → (Dn n) := fun x => if (x.1 = true) then (f_ref n x) else (f_no_ref n x)

theorem h_def_op : Dn_op n = (fun x => if (x.1 = true) then (f_ref n x) else (f_no_ref n x)) := rfl

theorem h_def_ref : f_ref n x = fun y => if (y.1 = true) then {1 := false, 2 := Fin.sub x.2 y.2} else {1 := true, 2 := Fin.sub x.2 y.2} := rfl

theorem h_def_no_ref : f_no_ref n x = fun y => if (y.1 = true) then {1 := true, 2 := Fin.add x.2 y.2} else {1 := false, 2 := Fin.add x.2 y.2} := rfl

theorem h_op_t {x : Dn n} : x.1 = true → (Dn_op n x = f_ref n x) := by
  intro h
  rw[h_def_op]
  exact if_pos h

theorem h_op_f {x : Dn n} : x.1 = false → (Dn_op n x = f_no_ref n x) := by
  intro h
  rw[h_def_op]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2

theorem h_ref_t {x y : Dn n} : y.1 = true → (f_ref n x y = {1 := false, 2 := Fin.sub x.2 y.2}) := by
  intro h
  rw[h_def_ref]
  exact if_pos h

theorem h_no_ref_t {x y : Dn n}: y.1 = true → (f_no_ref n x y= {1 := true, 2 := Fin.add x.2 y.2}) := by
  intro h
  rw[h_def_no_ref]
  exact if_pos h

theorem h_no_ref_f {x y : Dn n}: y.1 = false → (f_no_ref n x y= {1 := false, 2 := Fin.add x.2 y.2}) := by
  intro h
  rw[h_def_no_ref]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2

theorem h_ref_f {x y : Dn n}: y.1 = false → (f_ref n x y= {1 := true, 2 := Fin.sub x.2 y.2}) := by
  intro h
  rw[h_def_ref]
  have h2 := ne_true_of_eq_false h
  exact if_neg h2


instance (n : ℕ) (hpos : NeZero n) : Defs.Group (Dn n) where
  op := Dn_op n

  id := {1 := False, 2:= 0}




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
          rw[h_op_t hat]
          rw[h_ref_t hbt]
          have hfr : (false, a.2.sub b.2).1 = false := rfl
          rw[h_op_f hfr]
          rw[h_no_ref_t hct]
          rw[h_op_t hbt]
          rw[h_ref_t hct]
          have hfl : (false, b.2.sub c.2).1 = false := rfl
          rw[h_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).add c.2 = a.2.sub (b.2.sub c.2)
          exact fun a b c => sub_add a.2 b.2 c.2
          specialize h a b c
          rw[h]
        | inr hcf =>
          rw[h_op_t hat]
          rw[h_ref_t hbt]
          have hfr : (false, a.2.sub b.2).1 = false := rfl
          rw[h_op_f hfr]
          rw[h_no_ref_f hcf]
          rw[h_op_t hbt]
          rw[h_ref_f hcf]
          have htl : (true, b.2.sub c.2).1 = true := rfl
          rw[h_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).add c.2 = a.2.sub (b.2.sub c.2)
          exact fun a b c => sub_add a.2 b.2 c.2
          specialize h a b c
          rw[h]
      | inr hbf =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw[h_op_t hat]
          rw[h_ref_f hbf]
          have htr : (true, a.2.sub b.2).1 = true := rfl
          rw[h_op_t htr]
          rw[h_ref_t hct]
          rw[h_op_f hbf]
          rw[h_no_ref_t hct]
          have htl : (true, b.2.add c.2).1 = true := rfl
          rw[h_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).sub c.2 = a.2.sub (b.2.add c.2)
          exact fun a b c => sub_sub a.2 b.2 c.2
          specialize h a b c
          rw[h]
        | inr hcf =>
          rw[h_op_t hat]
          rw[h_ref_f hbf]
          have htr : (true, a.2.sub b.2).1 = true := rfl
          rw[h_op_t htr]
          rw[h_ref_f hcf]
          rw[h_op_f hbf]
          rw[h_no_ref_f hcf]
          have hfl : (false, b.2.add c.2).1 = false := rfl
          rw[h_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.sub b.2).sub c.2 = a.2.sub (b.2.add c.2)
          exact fun a b c => sub_sub a.2 b.2 c.2
          specialize h a b c
          rw[h]
    | inr haf =>
      have h : b.1 = true ∨ b.1 = false
      exact Bool.eq_false_or_eq_true b.1
      cases h with
      | inl hbt =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw[h_op_f haf]
          rw[h_no_ref_t hbt]
          have htr : (true, a.2.add b.2).1 = true := rfl
          rw[h_op_t htr]
          rw[h_ref_t hct]
          rw[h_op_t hbt]
          rw[h_ref_t hct]
          have hfl : (false, b.2.sub c.2).1 = false := rfl
          rw[h_no_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).sub c.2 = a.2.add (b.2.sub c.2)
          exact fun a b c => add_sub_assoc a.2 b.2 c.2
          specialize h a b c
          rw[h]
        | inr hcf =>
          rw[h_op_f haf]
          rw[h_no_ref_t hbt]
          have htr : (true, a.2.add b.2).1 = true := rfl
          rw[h_op_t htr]
          rw[h_ref_f hcf]
          rw[h_op_t hbt]
          rw[h_ref_f hcf]
          have htl : (true, b.2.sub c.2).1 = true := rfl
          rw[h_no_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).sub c.2 = a.2.add (b.2.sub c.2)
          exact fun a b c => add_sub_assoc a.2 b.2 c.2
          specialize h a b c
          rw[h]
      | inr hbf =>
        have h : c.1 = true ∨ c.1 = false
        exact Bool.eq_false_or_eq_true c.1
        cases h with
        | inl hct =>
          rw[h_op_f haf]
          rw[h_no_ref_f hbf]
          have hfr : (false, a.2.add b.2).1 = false := rfl
          rw[h_op_f hfr]
          rw[h_no_ref_t hct]
          rw[h_op_f hbf]
          rw[h_no_ref_t hct]
          have htl : (true, b.2.add c.2).1 = true := rfl
          rw[h_no_ref_t htl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).add c.2 = a.2.add (b.2.add c.2)
          exact fun a b c => add_assoc a.2 b.2 c.2
          specialize h a b c
          rw[h]
        | inr hcf =>
          rw[h_op_f haf]
          rw[h_no_ref_f hbf]
          have hfr : (false, a.2.add b.2).1 = false := rfl
          rw[h_op_f hfr]
          rw[h_no_ref_f hcf]
          rw[h_op_f hbf]
          rw[h_no_ref_f hcf]
          have hfl : (false, b.2.add c.2).1 = false := rfl
          rw[h_no_ref_f hfl]
          simp
          have h : ∀ a b c : Dn n, (a.2.add b.2).add c.2 = a.2.add (b.2.add c.2)
          exact fun a b c => add_assoc a.2 b.2 c.2
          specialize h a b c
          rw[h]
    exact fun a => h_exact a

  inv := by
    sorry

  inv_op := by
    sorry

  op_id := by
    sorry

  id_op := by
    sorry
