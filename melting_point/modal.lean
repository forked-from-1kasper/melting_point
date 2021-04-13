noncomputable theory
open classical

notation `⊥` := false
notation `⊤` := true

axiom necessary : Prop → Prop
prefix `□`:1024 := necessary

def possible (p : Prop) := ¬□¬p
prefix `◇`:1024 := possible

variables {p q : Prop}

axiom N   : □⊤
axiom K   : □(p → q) → □p → □q
axiom T   : □p → p
axiom «4» : □p → □□p
axiom B   : p → ◇□p

axiom ens : Type
namespace ens
  axiom contains : ens → ens → Prop
  instance : has_mem ens ens := ⟨contains⟩

  axiom comp : (ens → Prop) → ens
  @[simp] axiom compβrule : Π (φ : ens → Prop) (x : ens), (x ∈ comp φ) = □(φ x)

  axiom setext.intro : ∀ {α β : ens}, (∀ x, x ∈ α ↔ x ∈ β) → α = β

  def setext.elim {α β : ens} : α = β → (∀ x, x ∈ α ↔ x ∈ β) :=
  begin intro p, induction p, intro x, apply iff.refl end

  def setext {α β : ens} : (∀ x, x ∈ α ↔ x ∈ β) ↔ (α = β) :=
  ⟨setext.intro, setext.elim⟩

  def spec (f : ens → ens) := comp (λ y, ∃ x, f x = y)

  def map (α β : ens) (f : ens → ens) :=
  comp (λ y, ∃ x, x ∈ α ∧ y ∈ β ∧ f x = y)

  def bimap (α β : ens) (f : ens → ens → ens) :=
  comp (λ x, ∃ u v, u ∈ α ∧ v ∈ β ∧ x = f u v)

  def empty := comp (λ _, false)

  theorem {u} empty.elim {α : Sort u} {β : ens} : β ∈ empty → α :=
  begin intro p, simp [empty] at p, cases T p end

  def univ : ens := comp (λ _, true)

  def insert (x : ens) (α : ens) :=
  comp (λ y, x = y ∨ y ∈ α)
  instance : has_insert ens ens := ⟨insert⟩

  def sep (p : ens → Prop) (s : ens) :=
  comp (λ x, x ∈ s ∧ p x)
  instance : has_sep ens ens := ⟨sep⟩

  @[simp] def insertβrule (x y : ens) (α : ens) :
    (x ∈ insert y α) = □(y = x ∨ x ∈ α) := 
  by simp [insert]

  def union (α β : ens) := comp (λ x, x ∈ α ∨ x ∈ β)
  def diff  (α β : ens) := {x ∈ α | x ∉ β}
  def inter (α β : ens) : ens := {x ∈ α | x ∈ β}
  def subset (α β : ens) := ∀ x, x ∈ α → x ∈ β
  def compl (α : ens) := comp (λ x, x ∉ α)

  instance : has_emptyc ens := ⟨empty⟩
  instance : has_union ens  := ⟨union⟩
  instance : has_inter ens  := ⟨inter⟩
  instance : has_subset ens := ⟨subset⟩
  instance : has_neg ens    := ⟨compl⟩
  instance : has_sdiff ens  := ⟨diff⟩
  
  instance : has_singleton ens ens := ⟨λ x, insert x ∅⟩

  def singleton.id {α : ens} : α ∈ (singleton α : ens) :=
  begin simp [singleton, has_insert.insert], apply N end

  def sUnion (α : ens) : ens := comp (λ t, ∃ x ∈ α, t ∈ x)
  prefix ⋃₀ := sUnion

  def powerset (α : ens) := comp (⊆ α)
  prefix `𝒫` := powerset

  def R : ens := comp (λ x, x ∉ x)
  def R.irrefl : R ∉ R := begin
    unfold R, rw [compβrule], intro H,
    have G := T H, rw [compβrule] at G,
    apply G, assumption
  end

  /-
  def Russell : R ∈ R ↔ R ∉ R := begin
    unfold R, split; intro H,
    { rw [compβrule] at H, apply T H },
  -- modal collapse implies contradiction here
    { rw [compβrule], admit }
  end
  -/
end ens