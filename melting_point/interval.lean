import melting_point.core

universe u

def I.rel (f g : ℕ → 𝟐) : Prop :=
∃ (n : ℕ),
  (∀ m, m < n → f m = g m) ∧
  (f n = ff ∧ g n = tt) ∧
  (∀ m, m > n → f m = tt ∧ g m = ff)

def I := quot I.rel
def I.elem : (ℕ → 𝟐) → I := quot.mk I.rel

def i₀ := I.elem (λ _, ff)
def i₁ := I.elem (λ _, tt)

instance : has_zero I := ⟨i₀⟩
instance : has_one I  := ⟨i₁⟩

def halve.aux (f : ℕ → 𝟐) : ℕ → 𝟐
|    0    := ff
| (n + 1) := f n

def halve : I → I := begin
  fapply quot.lift,
  { intro f, apply I.elem, apply halve.aux f },
  { intros a b H, apply quot.sound,
    cases H with n H, cases H with h g, cases g with g f,
    existsi (n + 1), split,
    { intros m H, induction m with m ih,
      { reflexivity },
      { apply h, change nat.succ m ≤ n,
        fapply le_of_add_le_add_right,
        exact 1, exact H } }, split,
    { exact g },
    { intros m H, induction m with m ih,
      { cases H },
      { apply f, change nat.succ n ≤ m,
        fapply le_of_add_le_add_right,
        exact 1, exact H } } }
end