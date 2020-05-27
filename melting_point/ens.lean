noncomputable theory
open classical

axiom cls : Type
axiom V   : set cls

def ens := subtype V

namespace cls
  axiom contains : ens → cls → Prop
  instance : has_mem ens cls := ⟨contains⟩

  axiom comp : (ens → Prop) → cls
  @[simp] axiom compβrule : Π (φ : ens → Prop) (x : ens), (x ∈ comp φ) = φ x
  axiom ext : ∀ {α β : cls}, (∀ x, x ∈ α ↔ x ∈ β) → α = β

  def empty := comp (λ _, false)
  def univ  := comp (λ _, true)

  def insert (x : ens) (α : cls) :=
  comp (λ y, x = y ∨ y ∈ α)
  instance : has_insert ens cls := ⟨insert⟩

  def sep (φ : ens → Prop) (α : cls) :=
  comp (λ x, x ∈ α ∧ φ x)
  instance : has_sep ens cls := ⟨sep⟩

  def union  (α β : cls) := comp {x | x ∈ α ∨ x ∈ β}
  def diff   (α β : cls) := {x ∈ α | x ∉ β}
  def inter  (α β : cls) := {x ∈ α | x ∈ β}
  def subset (α β : cls) := ∀ x, x ∈ α → x ∈ β
  def compl  (α : cls)   := comp {x | x ∉ α}

  instance : has_emptyc cls := ⟨empty⟩
  instance : has_union  cls := ⟨union⟩
  instance : has_inter  cls := ⟨inter⟩
  instance : has_subset cls := ⟨subset⟩
  instance : has_neg    cls := ⟨compl⟩
  instance : has_sdiff  cls := ⟨diff⟩

  def powerset (α : cls) : cls := comp {β | β.val ⊆ α}
  prefix `𝒫`:100 := powerset
end cls

namespace ens
  axiom empty     : ∅ ∈ V
  axiom singleton : ∀ x, {x} ∈ V
  axiom union     : ∀ α β, α ∈ V → β ∈ V → α ∪ β ∈ V
  axiom inter     : ∀ α β, α ∈ V → β ∈ V → α ∩ β ∈ V
  axiom diff      : ∀ α β, α ∈ V → β ∈ V → α \ β ∈ V
  axiom powerset  : ∀ (α : cls), α ∈ V → 𝒫 α ∈ V
  axiom sep       : ∀ (φ : ens → Prop) (α : cls), α ∈ V → { x ∈ α | φ x } ∈ V
end ens