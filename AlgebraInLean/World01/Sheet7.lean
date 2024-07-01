import AlgebraInLean.World01.Sheet6
open Defs

def Sn (n : ℕ) : Type := {f : Fin n → Fin n // Function.Bijective f}

def Sn_op {n : ℕ} (f g : Sn n) : Sn n := {val := f.val ∘ g.val , property := Function.Bijective.comp f.property g.property}

theorem op_def (n : ℕ) {f g : Sn n} : Sn_op f g = {val := f.val ∘ g.val , property := Function.Bijective.comp f.property g.property} := rfl

theorem inverse (f : Fin n → Fin n) (h : Function.Bijective f) : ∃ g : Fin n → Fin n, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  exact Function.bijective_iff_has_inverse.mp h

noncomputable def Sn_inv_val : (Sn n) → (Fin n → Fin n) := fun f => (inverse f.val f.property).choose

theorem Sn_inv_def (f : Sn n) : Sn_inv_val f = (inverse f.val f.property).choose := rfl

theorem inverse_prop (f : Sn n) : Function.LeftInverse (Sn_inv_val f) f.val ∧ Function.RightInverse (Sn_inv_val f) f.val := by
  rw[Sn_inv_def]
  exact (inverse f.val f.property).choose_spec

noncomputable def Sn_inv : (Sn n) → (Sn n) := fun f => {val := Sn_inv_val f, property := by have h:= inverse_prop f; rw[Function.bijective_iff_has_inverse]; use f.val; exact And.comm.mp h}

@[ext]
theorem Sn.ext {n : ℕ} {f g : Sn n} : f.val = g.val → f = g := by
  intro h
  unfold Sn at *
  ext
  rw [h]
  done

def Sn_id : Sn n := {val := id, property := Function.bijective_id}

noncomputable instance (n : ℕ) : Defs.Group (Sn n) where
  op := Sn_op

  op_assoc := by
    intro a b c
    rfl

  id := Sn_id

  op_id := by
    intro a
    rfl

  id_op := by
    intro a
    rfl

  inv := Sn_inv

  inv_op := by
    have h : ∀ a : Sn n, (Sn_op) (Sn_inv a) a = Sn_id
    intro a
    have h2 :  (Sn_op (Sn_inv a) a).val = Sn_id.val
    rw[op_def n]
    simp
    have h_inverse_prop := inverse_prop a
    obtain ⟨hl, _⟩ := h_inverse_prop
    exact Function.RightInverse.id hl
    ext
    rw[h2]
    exact fun a => h a
    done
