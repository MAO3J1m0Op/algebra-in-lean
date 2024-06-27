import Mathlib.Tactic

/- Sheet 6
list of tactics for the user to keep updating -/

/- Tactics!

rfl
rw
done
sorry
intro
exact
apply
trivial
exfalso
cases
induction
have
assumption
specialize
left
right
constructor
nth_rewrite
use
simp
symm
-/

/-IGNORE ALL THIS BELOW I'm just storing it here for organizational purposes-/

/-Levels from Natural Number Game-/



/-Advanced Addition World Level 5-/
example (a b : Nat) : a + b = 0 → a = 0 := by
  induction b with
  | zero =>
    intro h1
    rw[add_zero] at h1
    exact h1
  | succ n ih =>
    sorry

/-Inequality World Level 4-/
example (x y z : Nat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry


/- select exercises from Kevin Buzzard's Formalizing Mathematics
to be borrowed with credit given or modified.-/

variable (P Q R S T : Prop)

/-Section 1 Sheet 4-/

example : P ∧ Q → P := by
  intro h1
  cases h1 with
  | intro left right =>
    exact left
  done

example : P ∧ Q → Q := by
  intro h1
  cases h1 with
  | intro left right =>
    exact right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases h2 with
  | intro left right =>
    apply h1
    exact left
    exact right
  done

example : P → Q → P ∧ Q := by
  intro h1 h2
  constructor
  · exact h1
  · exact h2
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  cases h1 with
  | intro left right =>
    constructor
    · exact right
    · exact left
  done

example : P → P ∧ True := by
  intro h1
  constructor
  · exact h1
  · trivial
  done

example : False → P ∧ False := by
  intro h1
  constructor
  · exfalso
    exact h1
  · exact h1
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases h1 with
  | intro left1 right1 =>
    cases h2 with
    | intro left2 right2 =>
      constructor
      · exact left1
      · exact right2
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  · exact h2
  · exact h3
  done

/-Section 1 Sheet 5-/
example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw[h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro h1
    rw[h1]
  · intro h2
    rw[h2]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rw[h2] at h1
  exact h1
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h1
    cases h1 with
    | intro left right =>
      constructor
      exact right
      exact left
  · intro h2
    cases h2 with
    | intro left right =>
      constructor
      · exact right
      · exact left
  done

/-Section 1 Sheet 6-/

example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  cases h1 with
  | inl h =>
    apply h2 at h
    exact h
  | inr h =>
    apply h3 at h
    exact h
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases h1 with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h1
    cases h1 with
    | inl h2 =>
      cases h2 with
      | inl h3 =>
        left
        exact h3
      | inr h3 =>
        right
        left
        exact h3
    | inr h4 =>
      right
      right
      exact h4
  · intro h5
    cases h5 with
    | inl h6 =>
      left
      left
      exact h6
    | inr h6 =>
      cases h6 with
      | inl h7 =>
        left
        right
        exact h7
      | inr h7 =>
        right
        exact h7
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  cases h3 with
  | inl h4 =>
    apply h1 at h4
    left
    exact h4
  | inr h4 =>
    apply h2 at h4
    right
    exact h4
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  cases h2 with
  | inl h3 =>
    apply h1 at h3
    left
    exact h3
  | inr h3 =>
    right
    exact h3
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  · intro h3
    cases h3 with
    | inl h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          left
          apply h5 at h4
          exact h4
    | inr h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          right
          apply h7 at h4
          exact h4
  · intro h3
    cases h3 with
    | inl h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          left
          apply h6 at h4
          exact h4
    | inr h4 =>
      cases h1 with
      | intro h5 h6 =>
        cases h2 with
        | intro h7 h8 =>
          right
          apply h8 at h4
          exact h4
  done
