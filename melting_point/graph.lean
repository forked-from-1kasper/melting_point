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

inductive nonzero : ord → Prop
| succ {x : ord}     : nonzero (ord.succ x)
| lim  {f : ℕ → ord} : nonzero (ord.lim f)

def ω := ord.lim ord.finite

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
  def G : graph Koenigsberg
  | Kneiphof Lomse    := 1
  | Altstadt Lomse    := 1
  | Lomse    Vorstadt := 1
  | Altstadt Kneiphof := 2
  | Altstadt Vorstadt := 2
  | _        _        := 0

  def G' := undirected G
end Koenigsberg

end melting_point.graph