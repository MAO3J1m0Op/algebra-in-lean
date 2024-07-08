import AlgebraInLean.World01.Sheet6

namespace AlgebraInLean

/- The last group we will cover in this section is the symmetric group. This is
defined by the different ways of permuting n elements. The group operation is
composition. For example, S3 has 6 elements, which permute (1, 2, 3) into
(1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), and (3, 2, 1). Elements
in Sn can also be thought of as bijective, or invertable, functions. We can
write an element in Sn as a function from Fin n to Fin n, along with a proof
that that functoin is bijective.-/
def Sn (n : ℕ) : Type := {f : Fin n → Fin n // Function.Bijective f}

/- The group operation is function composition, along with a proof that the composition
of two bijective functions is also bijective.-/
def Sn_op {n : ℕ} (f g : Sn n) : Sn n := {val := f.val ∘ g.val , property := Function.Bijective.comp f.property g.property}

/- Again, we rewrite the definition as a theorem for ease of use-/
theorem op_def (n : ℕ) {f g : Sn n} : Sn_op f g = {val := f.val ∘ g.val , property := Function.Bijective.comp f.property g.property} := rfl

/- Finding the inverse function is tricky. Since elements of Sn are bijections,
there must exist an inverse, but knowing that something exists and actually finding
the value are different tasks. This theorem shows that an inverse must exist.-/
theorem inverse_exists (f : Fin n → Fin n) (h : Function.Bijective f) : ∃ g : Fin n → Fin n, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  exact Function.bijective_iff_has_inverse.mp h

/- This computes the value of the inverse function, but does not have a proof that
the inverse is a bijection, so it isn't an element of Sn yet. This uses .choose,
which extracts a value from a ∃ statement. The noncomputable keyword means that
the computer cannot actually compute the value, and can only give it a name.-/
noncomputable def Sn_inv_val : (Sn n) → (Fin n → Fin n) := fun f => (inverse_exists f.val f.property).choose

/- Restating the definition as a theorem again.-/
theorem Sn_inv_def (f : Sn n) : Sn_inv_val f = (inverse_exists f.val f.property).choose := rfl

/- This uses .choose_spec, which shows that elements chosen through .choose retain
the property that the ∃ implies. This example shows that the inverse chosen is
actually an inverse.-/
theorem inverse_prop (f : Sn n) : Function.LeftInverse (Sn_inv_val f) f.val ∧ Function.RightInverse (Sn_inv_val f) f.val := by
  rw [Sn_inv_def]
  exact (inverse_exists f.val f.property).choose_spec

/- Now, using the value gotten earlier along with the proof that the inverse is an inverse,
we can proove that the inverse is a bijection, so we can write it as an element of
Sn and complete the definition of the inverse.-/
noncomputable def Sn_inv : (Sn n) → (Sn n) := fun f => {val := Sn_inv_val f, property := by have h:= inverse_prop f; rw [Function.bijective_iff_has_inverse]; use f.val; exact And.comm.mp h}

/- This theorem allows us to extract the function value from an object in Sn.
This means that if we can proove that two functions are equal, the Sn objects
they represent are equal.-/
@[ext]
theorem Sn.ext {n : ℕ} {f g : Sn n} : f.val = g.val → f = g := by
  intro h
  unfold Sn at *
  ext
  rw [h]
  done

/- We define the identity as the identity function.-/
def Sn_id : Sn n := {val := id, property := Function.bijective_id}

noncomputable instance (n : ℕ) : Group (Sn n) where
  op := Sn_op

  op_assoc := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a b c
    rfl
    -- END OF SAMPLE SOLUTION

  id := Sn_id

  op_id := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    rfl
    -- END OF SAMPLE SOLUTION

  id_op := by
    -- sorry
    -- SAMPLE SOLUTION
    intro a
    rfl
    -- END OF SAMPLE SOLUTION

  inv := Sn_inv

  /- Prooving inv_op is more involved than the other group axioms. If you get
  stuck, look at the proofs in the other sheets for help. Also remember to use
  ext to turn a goal that two Sn objects are equal into having to show that the
  two corresponding functions are equal.-/
  inv_op := by
    -- sorry
    -- SAMPLE SOLUTION
    have h : ∀ a : Sn n, (Sn_op) (Sn_inv a) a = Sn_id
    intro a
    have h2 :  (Sn_op (Sn_inv a) a).val = Sn_id.val
    rw [op_def n]
    simp
    have h_inverse_prop := inverse_prop a
    obtain ⟨hl, _⟩ := h_inverse_prop
    exact Function.RightInverse.id hl
    ext
    rw [h2]
    exact fun a => h a
    -- END OF SAMPLE SOLUTION
