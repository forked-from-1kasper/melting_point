namespace melting_point.set

universe u

theorem union.comm {α : Type u} (a b : set α) : a ∪ b = b ∪ a :=
begin funext x, apply propext, apply or.comm end

theorem inter.comm {α : Type u} (a b : set α) : a ∩ b = b ∩ a :=
begin funext x, apply propext, apply and.comm end

theorem union.empty {α : Type u} (a : set α) : a ∪ ∅ = a := begin
  funext x, apply propext, split,
  { intro h, cases h, exact h, cases h },
  { apply or.inl }
end

theorem inter.empty {α : Type u} (a : set α) : a ∩ ∅ = ∅ := begin
  funext x, apply propext, split; intro h,
  { cases h with a b, cases b },
  { cases h }
end

theorem union.univ {α : Type u} (a : set α) : a ∪ set.univ = set.univ := begin
  funext x, apply propext, split; intro h,
  { cases h; trivial },
  { apply or.inr, assumption }
end

theorem inter.univ {α : Type u} (a : set α) : a ∩ set.univ = a := begin
  funext x, apply propext, split; intro h,
  { cases h with n m, exact n },
  { split, exact h, trivial }
end

theorem union.id {α : Type u} (a : set α) : a ∪ a = a := begin
  funext x, apply propext, split,
  { intro h, cases h with a b, exact a, exact b },
  { intro h, apply or.inl, exact h }
end

theorem inter.id {α : Type u} (a : set α) : a ∩ a = a := begin
  funext x, apply propext, split,
  { intro h, cases h with a b, exact a },
  { intro h, split, repeat { exact h } }
end

def countable {α : Type u} (s : set α) :=
∃ (f : subtype s → ℕ), function.injective f

end melting_point.set