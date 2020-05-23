-- Naive set theory

noncomputable theory
open classical

axiom ens : Type
namespace ens
  axiom contains : ens → ens → Prop
  instance : has_mem ens ens := ⟨contains⟩

  axiom comp : (ens → Prop) → ens
  @[simp] axiom compβrule : Π (φ : ens → Prop) (x : ens), (x ∈ comp φ) = φ x
  axiom setext.intro : ∀ {α β : ens}, (∀ x, x ∈ α ↔ x ∈ β) → α = β

  def setext.elim {α β : ens} : α = β → (∀ x, x ∈ α ↔ x ∈ β) :=
  begin intro p, induction p, intro x, apply iff.refl end

  def setext {α β : ens} : (∀ x, x ∈ α ↔ x ∈ β) ↔ (α = β) :=
  ⟨setext.intro, setext.elim⟩

  def spec (f : ens → ens) := comp (λ y, ∃ x, f x = y)
  def bimap (f : ens → ens → ens) :=
  comp (λ x, ∃ u v, x = f u v)

  def empty := comp (λ _, false)

  theorem {u} empty.elim {α : Sort u} {β : ens} : β ∈ empty → α :=
  begin intro p, simp [empty] at p, induction p end

  def univ : ens := comp (λ _, true)

  def insert (x : ens) (α : ens) :=
  comp (λ y, x = y ∨ y ∈ α)
  instance : has_insert ens ens := ⟨insert⟩

  def sep (p : ens → Prop) (s : ens) :=
  comp (λ x, x ∈ s ∧ p x)
  instance : has_sep ens ens := ⟨sep⟩

  @[simp] def insertβrule (x y : ens) (α : ens) : (x ∈ insert y α) = (y = x ∨ x ∈ α) := 
  by simp [insert]

  def union (α β : ens) := {x ∈ α | x ∈ β}
  def diff  (α β : ens) := {x ∈ α | x ∉ β}
  def inter (α β : ens) : ens := comp (λ x, x ∈ α ∨ x ∈ β)
  def subset (α β : ens) := ∀ x, x ∈ α → x ∈ β
  def compl (α : ens) := comp (λ x, x ∉ α)

  instance : has_emptyc ens := ⟨empty⟩
  instance : has_union ens  := ⟨union⟩
  instance : has_inter ens  := ⟨inter⟩
  instance : has_subset ens := ⟨subset⟩
  instance : has_neg ens    := ⟨compl⟩
  instance : has_sdiff ens  := ⟨diff⟩

  def singleton.id {α : ens} : α ∈ (singleton α : ens) :=
  by simp [singleton, has_insert.insert]

  def sUnion (α : ens) : ens := comp (λ t, ∃ x ∈ α, t ∈ x)
  prefix ⋃₀ := sUnion

  def powerset (α : ens) := comp (⊆ α)
  prefix `𝒫` := powerset

  def unord (α β : ens) : ens := {α, β}
  def pair (α β : ens) : ens := {{α}, {α, β}}
  def prod (α β : ens) : ens := bimap pair
  local infix × := prod

  lemma unord.left {α β : ens} : α ∈ unord α β :=
  begin simp [unord, has_insert.insert, singleton] end

  lemma unord.right {α β : ens} : β ∈ unord α β :=
  begin simp [unord, has_insert.insert] end

  def singleton.eq {α β : ens} : @eq ens {α} {β} → α = β := begin
    intro p, have q := (setext.elim p α).mp singleton.id,
    simp [singleton, has_insert.insert] at q, induction q,
    { symmetry, assumption },
    { apply empty.elim q }
  end

  def unord.eq {α β α' β' : ens} : unord α β = unord α' β' →
    (α = α' ∧ β = β') ∨ (α = β' ∧ β = α') := begin
    intro x,
    have p := (setext.elim x α).mp unord.left,
    have q := (setext.elim x β).mp unord.right,
    have r := (setext.elim x α').mpr unord.left,
    have s := (setext.elim x β').mpr unord.right,
    simp [unord, has_insert.insert, singleton] at p q r s,
    repeat { induction p <|> induction q <|> induction r <|> induction s },
    repeat { { left, split; refl } <|> { right, split; refl } <|>
             { apply empty.elim, assumption } }
  end

  def pair.eq {α β α' β' : ens} : pair α β = pair α' β' → α = α' ∧ β = β' := begin
    intro p, simp [pair] at p,
    cases unord.eq p with q,
    { induction q with u v, 
      have q := singleton.eq u, split,
      { assumption },
      { cases unord.eq v with x y,
        { cases x, assumption },
        { cases y with r s,
          transitivity, exact s,
          transitivity, symmetry, exact q,
          exact r } } },
    { induction h with r s, split,
      { have q := (setext.elim r α').mpr unord.left,
        simp [singleton, has_insert.insert] at q,
        induction q, assumption, apply empty.elim q },
      { have a := (setext.elim r β').mpr unord.right,
        have b := (setext.elim s β).mp   unord.right,
        have c := (setext.elim r α').mpr unord.left,
        simp [singleton, has_insert.insert,
              has_emptyc.emptyc, empty] at a b c,
        transitivity, { symmetry, exact b },
        transitivity, { symmetry, exact c },
        exact a } }
  end

  structure function (α β : ens) :=
  (map : ens) (sub : map ⊆ (α × β))
  (uniq : ∀ u, u ∈ α → ∃! v, pair u v ∈ map)

  infix ` ⟶ `:30 := function

  def function.intro {α β : ens} (f : ens → ens) : α ⟶ β :=
  ⟨spec (λ x, pair x (f x)),
   begin
     intros y p, simp [spec] at p,
     induction p with x p, induction p,
     simp [prod, bimap], existsi x, existsi f x,
     trivial
   end,
   begin
     intros u p, existsi f u, split,
     { simp [spec], existsi u, trivial },
     { intros x q, simp [spec] at q, induction q with y q,
       have r := pair.eq q, induction r with r s,
       induction r, induction s, reflexivity }
   end⟩

  def une : ens := {∅}
  notation `𝟙` := une

  def bool : ens := {∅, 𝟙}
  def not : bool ⟶ bool :=
  function.intro (λ x, match prop_decidable (x = ∅) with
  | is_true _  := 𝟙
  | is_false _ := ∅
  end)

  lemma univ_in_univ : univ ∈ univ :=
  by simp [univ]

  def R : ens := comp (λ x, x ∉ x)
  def Russell : R ∈ R ↔ R ∉ R := begin
    unfold R, split,
    { intro H, rw [compβrule] at H, assumption },
    { intro H, rw [compβrule], assumption }
  end

  -- la fin
  def exfalso : false :=
  match prop_decidable (R ∈ R) with
  | is_true h  := absurd h (Russell.mp h)
  | is_false h := absurd (Russell.mpr h) h
  end
end ens
