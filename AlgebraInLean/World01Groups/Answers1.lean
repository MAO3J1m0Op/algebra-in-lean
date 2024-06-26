class Magma (G:Type) (f: G → G → G)

class Semigroup (G:Type) (f: G → G → G) where
  assoc: ∀ (a b c : G), f (f a b) c = f a (f b c)


class Monoid (G:Type) (f: G → G → G) where
  assoc: ∀ (a b c : G), f (f a b) c = f a (f b c)
  e: G
  id: ∀ a : G, f a e = a ∧ f e a = a
def eMonoid [Monoid G f] : G := Monoid.e f
def idl [Monoid G f] (a : G) : f a (Monoid.e f) = a := And.left (Monoid.id a)
def idr [Monoid G f] (a : G) : f (Monoid.e f) a = a := And.right (Monoid.id a)

#check Monoid.assoc
class Group (G:Type) (f: G → G → G) where
  assoc: ∀ (a b c : G), f (f a b) c = f a (f b c)
  e : G
  id: ∀ a : G, f a e = a ∧ f e a = a
  inverse: ∀ a : G, ∃ i : G , f a i = e ∧ f i a = e

class AbelianGroup (G:Type) (f: G → G → G) where
  assoc: ∀ (a b c : G), f (f a b) c = f a (f b c)
  e : G
  id: ∀ a : G, f a e = a ∧ f e a = a
  inverse: ∀ a : G, ∃ i : G , f a i = e ∧ f i a = e
  comm: ∀ a b : G, f a b = f b a


class Subgroup (G: Type) (f : G → G → G) [Group G f] where
  -- S: Type
  -- subset: ∀ (a : S)
  -- closedComp: ∀ (a b : S) f a b : S
  -- closedInv: ∀ (a : S) true

theorem id_unique [Magma M f] (e1 e2: M) :
  (∀ a : M, f a e1 = a ∧ f e1 a = a) → (∀ a : M, f a e2 = a ∧ f e2 a = a) → e1 = e2 := by
    intro he1 he2
    specialize he1 e2
    specialize he2 e1
    cases he1 with
    | intro he2e1 he1e2 =>
    cases he2 with
    | intro he1e2b he2e1b =>
    rw[←he1e2b]
    exact he1e2
    done
theorem inv_unique (M : Type) {f : M → M → M} [Monoid M f] (a i j : M) :
  (f a i = Monoid.e f ∧ f i a = Monoid.e f) → (f a j = Monoid.e f ∧ f j a = Monoid.e f) → i = j := by
    intro hi hj
    cases hi with
    | intro hai hia =>
    cases hj with
    | intro haj hja =>
    have hidri: f (Monoid.e f) i = i := idr i
    have hidlj: f j (Monoid.e f) = j := idl j
    rw[←hidri,←hidlj]
    calc f (Monoid.e f) i
      _ = f (f j a) i := by rw [hja]
      _ = f j (f a i) := Monoid.assoc j a i
      _ = f j (Monoid.e f) := by rw[←hai]
    done
