import melting_point.core

namespace melting_point.graph
universes u v

def nat.cases {α : Sort u} (zero : α) (succ : α → α) : ℕ → α
| 0       := zero
| (n + 1) := succ (nat.cases n)

inductive ord
| zero
| succ : ord → ord
| lim  : (ℕ → ord) → ord

def ord.add : ord → ord → ord
| ord.zero y     := y
| (ord.succ x) y := ord.succ (ord.add x y)
| (ord.lim f) y  := ord.lim (λ n, ord.add (f n) y)

instance : has_zero ord := ⟨ord.zero⟩
instance : has_one ord  := ⟨ord.succ 0⟩
instance : has_add ord  := ⟨ord.add⟩

def ord.finite : ℕ → ord :=
nat.cases ord.zero ord.succ

inductive iszero : ord → Prop
| intro : iszero 0

instance iszero.dec : decidable_pred iszero := begin
  intro x, cases x,
  { apply decidable.is_true, exact iszero.intro },
  repeat { apply decidable.is_false, intro h, cases h }
end

def nonzero : ord → Prop := not ∘ iszero

def ω := ord.lim ord.finite

def graph (α : Type u) := α → α → ord

def flat {α : Type u} (G : graph α) : α → α → Prop :=
λ x y, nonzero (G x y)

inductive R {α : Type u} (φ : α → α → Prop) : α → α → Prop
| refl  {x : α}   : R x x
| intro {x y : α} : φ x y → R x y

def S {α : Type u} (φ : α → α → Prop) :=
λ x y, φ x y ∨ φ y x

inductive T {α : Type u} (φ : α → α → Prop) : α → α → Prop
| intro {x y : α}   : φ x y → T x y
| trans {x y z : α} : T x y → T y z → T x z

def E {α : Type u} (φ : α → α → Prop) := R (S (T φ))

def way  {α : Type u} (G : graph α) := T (flat G)
def path {α : Type u} (G : graph α) := E (flat G)

def path.inj {α : Type u} (G : graph α) {x y : α} : way G x y → path G x y :=
R.intro ∘ or.inl

def unidirectional {α : Type u} (G : graph α) :=
∀ x y, iszero (G x y) ∨ iszero (G y x)

def acyclic {α : Type u} (G : graph α) : Prop :=
∀ x, ¬way G x x

def full {α : Type u} (φ : α → α → Prop) :=
∀ x y, φ x y

def complete  {α : Type u} (G : graph α) := full (flat G)
def connected {α : Type u} (G : graph α) := full (path G)

def tree {α : Type u} (G : graph α) :=
connected G ∧ acyclic G

inductive Koenigsberg
| Altstadt | Kneiphof
| Lomse    | Vorstadt

namespace Koenigsberg
  def G : graph Koenigsberg
  | Kneiphof Lomse    := 1
  | Altstadt Lomse    := 1
  | Lomse    Vorstadt := 1
  | Altstadt Kneiphof := 2
  | Altstadt Vorstadt := 2
  | _        _        := 0
end Koenigsberg

end melting_point.graph