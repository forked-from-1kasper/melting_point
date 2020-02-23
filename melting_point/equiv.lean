universes u v
variables {α : Type u} {β : Type v}

def homotopy {α : Type u} {β : Type v} (f g : α → β) :=
Π x, f x = g x
infix ` ~ ` := homotopy

def linv (f : α → β) := ∃ g, g ∘ f ~ id
def rinv (f : α → β) := ∃ g, f ∘ g ~ id
def biinv (f : α → β) := rinv f ∧ linv f

def injection (f : α → β) :=
∀ x y, f x = f y → x = y

def surjection (f : α → β) :=
∀ y, ∃ x, y = f x

def equiv (α : Type u) (β : Type v) :=
∃ (f : α → β), biinv f
infix ` ≃ `:25 := equiv

@[refl] theorem equiv.refl (α : Type u) : α ≃ α :=
begin existsi id, split; existsi id; intro x; reflexivity end