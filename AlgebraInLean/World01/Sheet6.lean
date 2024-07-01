import AlgebraInLean.World01.Sheet5
open Defs

def Dn (n : ℕ) : Type := Bool × (Fin n)

def f_no_ref (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x y => if (y.1 = true) then {1 := true, 2 := Fin.add x.2 y.2} else {1 := false, 2 := Fin.add x.2 y.2}

def f_ref (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x y => if (y.1 = true) then {1 := false, 2 := Fin.sub x.2 y.2} else {1 := true, 2 := Fin.sub x.2 y.2}

def Dn_op (n : ℕ) : (Dn n) → (Dn n) → (Dn n) := fun x => if (x.1 = true) then (f_ref n x) else (f_no_ref n x)

def Dn_inv (n : ℕ) : (Dn n) → (Dn n) := fun x => if (x.1 = true) then {1 := true, 2 := x.2} else {1 := false, 2 := -x.2}

theorem h_def_inv : Dn_inv n x =  if (x.1 = true) then {1 := true, 2 := x.2} else {1 := false, 2 := -x.2} := rfl

theorem h_def_op : Dn_op n = (fun x => if (x.1 = true) then (f_ref n x) else (f_no_ref n x)) := rfl

theorem h_def_ref : f_ref n x = fun y => if (y.1 = true) then {1 := false, 2 := Fin.sub x.2 y.2} else {1 := true, 2 := Fin.sub x.2 y.2} := rfl

theorem h_def_no_ref : f_no_ref n x = fun y => if (y.1 = true) then {1 := true, 2 := Fin.add x.2 y.2} else {1 := false, 2 := Fin.add x.2 y.2} := rfl

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

instance (n : ℕ) (hpos : NeZero n) : Defs.Group (Dn n) where
  op := Dn_op n

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

  id := {1 := false, 2:= 0}

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
      rw [hzero, ht.symm]
      rfl
    | inr hf =>
      rw [h_op_f hf]
      have hf2 : (false, 0).1 = false := rfl
      rw [h_no_ref_f hf2]
      simp
      have hzero : a.2.add 0 = a.2 := add_zero a.2
      rw [hzero, hf.symm]
      rfl
    exact fun a => h a

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
      rw [hzero1, hzero2, ht.symm]
      rfl
    | inr hf =>
      rw [h_no_ref_f hf]
      simp
      have hzero1 : Fin.add 0 a.2 = 0 + a.2 := rfl
      have hzero2 : 0 + a.2 = a.2 := zero_add a.2
      rw [hzero1, hzero2, hf.symm]
      rfl
    exact fun a => h a

  inv := Dn_inv n

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
