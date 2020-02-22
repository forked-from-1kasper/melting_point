import melting_point.core

namespace melting_point.graph
universes u v

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

def ord.nat : ℕ → ord
| 0       := 0
| (n + 1) := ord.succ (ord.nat n)

inductive nonzero : ord → Prop
| succ {x : ord}     : nonzero (ord.succ x)
| lim  {f : ℕ → ord} : nonzero (ord.lim f)

def ω := ord.lim ord.nat

def graph (α : Type u) := α → α → ord

inductive path {α : Type u} (G : graph α) : α → α → Prop
| intro {x y : α}   : nonzero (G x y) → path x y
| trans {x y z : α} : path x y → path y z → path x z

def undirected {α : Type u} (G : graph α) : graph α :=
λ x y, match G x y, G y x with
| x, ord.zero := x
| _, y        := y
end

def acyclic {α : Type u} (G : graph α) : Prop :=
∀ x, ¬path G x x

def complete {α : Type u} (G : graph α) :=
∀ x y, nonzero (G x y)

def connected {α : Type u} (G : graph α) :=
∀ x y, path G x y

def tree {α : Type u} (G : graph α) :=
connected G ∧ acyclic G

inductive Koenigsberg
| Altstadt | Kneiphof
| Lomse    | Vorstadt

namespace Koenigsberg
  def G : Koenigsberg → Koenigsberg → Type
  | Kneiphof Lomse    := 𝟏
  | Altstadt Lomse    := 𝟏
  | Lomse    Vorstadt := 𝟏
  | Altstadt Kneiphof := 𝟐
  | Altstadt Vorstadt := 𝟐
  | _        _        := 𝟎
end Koenigsberg

end melting_point.graph