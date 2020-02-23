import melting_point.core melting_point.equiv

universes u v w

infix ` ⬝ ` := eq.trans
infix ` # ` := congr_arg
postfix ⁻¹ := eq.symm

theorem group_unit_is_unique {α : Type u} [group α] (e' : α)
  (right_unit' : Π x, x * e' = x)
  (one_mul' : Π x, e' * x = x)
  (H : 1 = e' → empty) : empty := begin
  have p := monoid.mul_one e',
  have q := one_mul' 1,
  apply H, transitivity,
  symmetry, repeat { assumption }
end

section
  variables {α : Type u} [group α]

  def group.natural_pow (x : α) : ℕ → α
  | 0 := 1
  | (n + 1) := x * group.natural_pow n

  def group.pow (x : α) : ℤ → α
  | (int.of_nat n) := group.natural_pow x n
  | -[1+ n] := group.natural_pow x⁻¹ (n + 1)

  instance nat_pow : has_pow α ℕ := ⟨group.natural_pow⟩
  instance int_pow : has_pow α ℤ := ⟨group.pow⟩
end

section
  variables {α : Type u} [group α]

  def square_is_unique (x : α)
    (h : x * x = x) : x = 1 := calc
      x = 1 * x : by symmetry; apply monoid.one_mul
    ... = (x⁻¹ * x) * x : by rw [←group.mul_left_inv x]; trivial
    ... = x⁻¹ * (x * x) : by apply monoid.mul_assoc
    ... = x⁻¹ * x : by rw [h]
    ... = 1 : by apply group.mul_left_inv
  
  theorem inv_of_inv (x : α) : (x⁻¹)⁻¹ = x := calc
    (x⁻¹)⁻¹ = 1 * (x⁻¹)⁻¹ : begin symmetry, apply monoid.one_mul end
        ... = (x * x⁻¹) * (x⁻¹)⁻¹ : by rw [mul_right_inv]
        ... = x * (x⁻¹ * x⁻¹⁻¹) : by apply monoid.mul_assoc
        ... = x * 1 : monoid.mul x # (mul_right_inv x⁻¹)
        ... = x : monoid.mul_one x

  theorem inverse_inj (a b : α) (h : a⁻¹ = b⁻¹) : a = b :=
  (inv_of_inv a)⁻¹ ⬝ (group.inv # h) ⬝ (inv_of_inv b)

  theorem reduce_left (a b c : α)
    (h : c * a = c * b) : a = b := calc
      a = 1 * a         : (monoid.one_mul a)⁻¹
    ... = (c⁻¹ * c) * a : (* a) # (group.mul_left_inv c)⁻¹
    ... = c⁻¹ * (c * a) : by apply monoid.mul_assoc
    ... = c⁻¹ * (c * b) : monoid.mul c⁻¹ # h
    ... = (c⁻¹ * c) * b : by symmetry; apply monoid.mul_assoc
    ... = 1 * b         : (* b) # (group.mul_left_inv c)
    ... = b             : monoid.one_mul b

  def identity_inv : (1 : α) = 1⁻¹ :=
  (mul_right_inv 1)⁻¹ ⬝ monoid.one_mul 1⁻¹

  def identity_sqr : (1 : α) = 1 * 1 :=
  begin symmetry, apply monoid.one_mul end

  theorem inv_uniq {a b : α} (h : a * b = 1) : a⁻¹ = b := calc
    a⁻¹ = a⁻¹ * 1 : (monoid.mul_one a⁻¹)⁻¹
    ... = a⁻¹ * (a * b) : monoid.mul a⁻¹ # h⁻¹
    ... = (a⁻¹ * a) * b : by symmetry; apply monoid.mul_assoc
    ... = 1 * b : (* b) # (group.mul_left_inv a)
    ... = b : by apply monoid.one_mul

  theorem inv_explode (x y : α) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := begin
    apply inv_uniq, calc
      (x * y) * (y⁻¹ * x⁻¹) = ((x * y) * y⁻¹) * x⁻¹ :
                              by symmetry; apply monoid.mul_assoc
                        ... = (x * 1) * x⁻¹ :
                              begin
                                apply congr_arg (* x⁻¹), transitivity,
                                { apply monoid.mul_assoc },
                                { apply congr_arg, apply mul_right_inv }
                              end
                        ... = x * x⁻¹ : (* x⁻¹) # (monoid.mul_one x)
                        ... = 1 : by apply mul_right_inv
  end
end

def commutes {α : Type u} [group α] (x y : α) :=
x * y = y * x

def zentrum (α : Type u) [group α] :=
{ z : α | Π g, commutes z g }

def Zentrum (α : Type u) [group α] :=
subtype (zentrum α)

def commutator {α : Type u} [group α] (g h : α) :=
g⁻¹ * h⁻¹ * g * h

def conjugate {α : Type u} [group α] (a x : α) :=
x⁻¹ * a * x

def conjugate_rev {α : Type u} [group α] (a x : α) :=
x * a * x⁻¹

def right_div {α : Type u} [group α] (x y : α) := x * y⁻¹
def left_div {α : Type u} [group α] (x y : α) := x⁻¹ * y

instance group_right_div {α : Type u} [group α] : has_div α := ⟨right_div⟩
instance group_left_div {α : Type u} [group α] : has_sdiff α := ⟨left_div⟩

instance conj_is_pow {α : Type u} [group α] : has_pow α α := ⟨conjugate⟩

theorem conjugate_distrib {α : Type u} [group α]
  (g x y : α) : g ^ (x * y) = (g ^ x) ^ y := calc
    g ^ (x * y) = (x * y)⁻¹ * (g * (x * y)) : by apply monoid.mul_assoc
            ... = (y⁻¹ * x⁻¹) * (g * (x * y)) :
                    (* g * (x * y)) # (inv_explode x y)
            ... = y⁻¹ * x⁻¹ * ((g * x) * y) :
                  begin
                    apply congr_arg (λ h, y⁻¹ * x⁻¹ * h),
                    symmetry, apply monoid.mul_assoc
                  end
            ... = y⁻¹ * (x⁻¹ * g * x) * y :
                  by repeat { rw [monoid.mul_assoc] }
            ... = (g ^ x) ^ y : by reflexivity

theorem conjugate_id {α : Type u} [group α] (g : α) : g ^ (1 : α) = g := calc
   g ^ (1 : α) = 1⁻¹ * g * 1 : by reflexivity
           ... = 1 * g * 1 : by rw [←identity_inv]
           ... = g * 1 : (* (1 : α)) # (monoid.one_mul g)
           ... = g : by apply monoid.mul_one

section
  variables {α : Type u} {β : Type v} [group α] [group β]

  def is_homo (φ : α → β) :=
  Π a b, φ (a * b) = φ a * φ b

  def homo (α : Type u) (β : Type v) [group α] [group β] :=
  { φ : α → β // is_homo φ }

  infix ` ⤳ `:20 := homo

  def homo.comp {α : Type u} {β : Type v} {φ : Type w} [group α] [group β] [group φ]
    (f : β ⤳ φ) (g : α ⤳ β) : α ⤳ φ := begin
    cases f with f F, cases g with g G,
    existsi f ∘ g, intros a b, calc
      (f ∘ g) (a * b) = f (g a * g b) : f # (G a b)
                  ... = (f ∘ g) a * (f ∘ g) b : by apply F
  end

  infix ` ⋅ `:60 := homo.comp

  def zero : α ⤳ β :=
  ⟨λ _, 1, λ _ _, (monoid.one_mul (1 : β))⁻¹⟩

  instance : has_zero (α ⤳ β) := ⟨zero⟩

  variable (φ : α ⤳ β)
  def ker : set α := { g | φ.val g = 1 }
  def Ker := subtype (ker φ)

  def im : set β := { g | ∃ f, φ.val f = g }
  def Im := subtype (im φ)
end

section
  variables {α : Type u} {β : Type v}

  def iso (α : Type u) (β : Type v) [group α] [group β] :=
  ∃ (f : α → β), is_homo f ∧ biinv f
  infix ` ≅ `:25 := iso

  @[refl] theorem iso.refl (α : Type u) [group α] : α ≅ α := begin
    existsi id, split,
    { intros a b, trivial },
    { split; existsi id; intro x; reflexivity }
  end
end

class is_subgroup {α : Type u} [group α] (φ : set α) :=
(unit : (1 : α) ∈ φ)
(mul : Π a b, a ∈ φ → b ∈ φ → a * b ∈ φ)
(inv : Π a, a ∈ φ → a⁻¹ ∈ φ)

def subgroup.mul {α : Type u} [group α] (φ : set α)
  [is_subgroup φ] (x y : subtype φ) : subtype φ := begin
  cases x with x h, cases y with y g, existsi (x * y),
  apply is_subgroup.mul; assumption
end

def subgroup.inv {α : Type u} [group α] (φ : set α)
  [is_subgroup φ] (x : subtype φ) : subtype φ := begin
  cases x with x h, existsi x⁻¹,
  apply is_subgroup.inv; assumption
end

instance subgroup.has_mul {α : Type u} [group α] (φ : set α)
  [is_subgroup φ] : has_mul (subtype φ) :=
⟨subgroup.mul φ⟩

instance subgroup.has_one {α : Type u} [group α] (φ : set α)
  [is_subgroup φ] : has_one (subtype φ) :=
⟨⟨1, is_subgroup.unit φ⟩⟩

class is_normal_subgroup {α : Type u} [group α] (φ : set α) extends is_subgroup φ :=
(cosets_eqv : Π {g h : α}, g * h ∈ φ → h * g ∈ φ)

section
  variables {α : Type u} [group α]
  theorem cancel_left (a b : α) : a = (a * b⁻¹) * b :=
  by rw [group.mul_assoc, group.mul_left_inv, group.mul_one]

  theorem cancel_right (a b : α) : a = (a * b) * b⁻¹ :=
  by rw [group.mul_assoc, mul_right_inv, group.mul_one]
end

theorem is_normal_subgroup.conj {α : Type u} [group α]
  (φ : set α) [is_normal_subgroup φ] (n g : α) : n ∈ φ → n ^ g ∈ φ := begin
  intro h, rw [cancel_right n g] at h,
  unfold has_pow.pow, unfold conjugate, rw [monoid.mul_assoc],
  apply is_normal_subgroup.cosets_eqv, assumption
end

theorem conjugate_subgroup_eqv {α : Type u} [group α]
  (φ : set α) [is_normal_subgroup φ] (a x : α) :
  conjugate a x ∈ φ → conjugate_rev a x ∈ φ := begin
  intro H, simp [conjugate_rev], simp [conjugate] at H,
  apply is_normal_subgroup.cosets_eqv,
  rw [←monoid.mul_assoc, mul_left_inv, monoid.one_mul],
  have G := is_normal_subgroup.cosets_eqv H,
  rw [←monoid.mul_assoc, mul_right_inv, monoid.one_mul] at G,
  assumption
end

section
  variables {α : Type u} [group α]

  /-
    gH = { g * h | h ∈ H }
    We have:
    1) h ∈ H
    2) g ∈ G
    3) (g * h) ∈ G

    g⁻¹ * (g * h) = x⁻¹ * y = h ∈ H
  -/
  def left_mul (φ : set α) [is_subgroup φ] : α → α → Prop :=
  λ x y, x⁻¹ * y ∈ φ

  def right_mul (φ : set α) [is_subgroup φ] : α → α → Prop :=
  λ x y, x * y⁻¹ ∈ φ

  def normal_subgroup_cosets {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] :
    Π x y, left_mul φ x y ↔ right_mul φ x y := begin
    intros x y, split; intro h,
    { simp [left_mul] at h, simp [right_mul],
      rw [cancel_right y⁻¹ x, ←group.mul_assoc],
      apply conjugate_subgroup_eqv,
      apply is_normal_subgroup.conj,
      rw [←inv_of_inv x, ←inv_explode],
      apply is_subgroup.inv, assumption },
    { simp [left_mul],
      rw [cancel_left y x, ←group.mul_assoc],
      apply is_normal_subgroup.conj,
      rw [←inv_of_inv y, ←inv_explode],
      apply is_subgroup.inv, assumption }
  end

  def normal_subgroup_cosets_eq {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] : left_mul φ = right_mul φ :=
  begin funext, apply propext, apply normal_subgroup_cosets end

  def factor_setoid_left (φ : set α) [is_subgroup φ] : setoid α :=
  let insert (x y z : α) : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := calc
    x⁻¹ * z = x⁻¹ * 1 * z : by rw [group.mul_one]
        ... = x⁻¹ * (y * y⁻¹) * z : by rw [mul_right_inv]
        ... = (x⁻¹ * y) * (y⁻¹ * z) : by repeat { rw [group.mul_assoc] }; trivial in
  ⟨left_mul φ,
   begin
     split, intro x, simp [left_mul], apply is_subgroup.unit,
     split, intros x y H, simp [left_mul] at *,
     rw [←inv_inv x, ←inv_explode],
     apply is_subgroup.inv, assumption,
     intros x y z G H, simp [left_mul] at *,
     rw [insert x y z], apply is_subgroup.mul; assumption
   end⟩

  def factor_setoid_right (φ : set α) [is_subgroup φ] : setoid α :=
  let insert (x y z : α) : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := calc
    x * z⁻¹ = x * 1 * z⁻¹ : by rw [group.mul_one]
        ... = x * (y⁻¹ * y) * z⁻¹ : by rw [mul_left_inv]
        ... = (x * y⁻¹) * (y * z⁻¹) : by repeat { rw [group.mul_assoc] }; trivial in
  ⟨right_mul φ,
   begin
    split, intro x, simp [right_mul], apply is_subgroup.unit,
    split, intros x y H, simp [right_mul] at *,
    rw [←inv_inv y, ←inv_explode],
    apply is_subgroup.inv, assumption,
    intros x y z G H, simp [right_mul] at *,
    rw [insert x y z], apply is_subgroup.mul; assumption
   end⟩

  def factor (α : Type u) [group α] (φ : set α) [is_subgroup φ] :=
  quotient (factor_setoid_left φ)
  infix `/` := factor

  def factor_right (α : Type u) [group α] (φ : set α) [is_subgroup φ] :=
  quotient (factor_setoid_right φ)
  infix `\` := factor_right

  def setoid.eq {α : Type} (x y : setoid α) (p : x.r = y.r) : x = y := begin
    tactic.unfreeze_local_instances, induction x, induction y,
    simp [*] at p, induction p, trivial
  end

  theorem factor_symmetry {α : Type} [group α]
    (φ : set α) [is_normal_subgroup φ] : α/φ = α\φ := begin
    apply congr_arg quotient,
    apply setoid.eq, apply normal_subgroup_cosets_eq
  end

  def factor.incl {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] : α → α/φ :=
  quot.mk (left_mul φ)

  def factor.mul {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] (x y : α/φ) : α/φ := begin
    apply @quotient.lift₂ α α _ (factor_setoid_left φ)
                          (factor_setoid_left φ) _ _ x y,
    { intros a b, exact factor.incl (a * b) },
    { intros a b c d p q, funext r, apply quot.sound,
      simp [left_mul], rw [←group.mul_assoc, group.mul_assoc b⁻¹],
      rw [cancel_left d b, group.mul_assoc, group.mul_assoc a⁻¹,
          ←group.mul_assoc c, ←group.mul_assoc a⁻¹,
          ←group.mul_assoc],
      apply is_normal_subgroup.conj,
      rw [←group.mul_assoc], apply is_subgroup.mul, exact p,
      rw [←inv_of_inv d, ←inv_explode], apply is_subgroup.inv,
      apply (normal_subgroup_cosets b d).mp; assumption },
  end

  instance factor.has_binop {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] : has_mul (α/φ) :=
  ⟨factor.mul⟩

  def factor.one {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] : α/φ :=
  factor.incl 1

  instance factor.has_one {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] : has_one (α/φ) :=
  ⟨factor.one⟩

  theorem factor.mul_one {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] (x : α/φ) : x * 1 = x := begin
    induction x, apply quot.sound, unfold left_mul,
    rw [inv_explode, monoid.mul_assoc, mul_left_inv, mul_left_inv],
    apply is_subgroup.unit, trivial
  end

  theorem factor.one_mul {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] (x : α/φ) : 1 * x = x := begin
    induction x, apply quot.sound, unfold left_mul,
    rw [inv_explode, monoid.mul_assoc, one_inv,
        monoid.one_mul, mul_left_inv],
    apply is_subgroup.unit, trivial
  end

  theorem factor.assoc {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] (x y z : α/φ) :
    x * y * z = x * (y * z) :=
  begin
    induction x, induction y, induction z,
    apply quot.sound, unfold left_mul, rw [monoid.mul_assoc],
    have p := eq.symm (mul_left_inv (x * (y * z))), induction p,
    apply is_subgroup.unit, repeat { trivial }
  end

  def factor.inv {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] (x : α/φ) : α/φ := begin
    apply @quotient.lift α (α/φ) (factor_setoid_left φ) _ _ x,
    { intro x, exact factor.incl x⁻¹ },
    { intros u v H, apply quot.sound,
      unfold left_mul, rw [inv_inv],
      apply (normal_subgroup_cosets u v).mp,
      repeat { assumption } }
  end

  theorem factor.left_inv {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] (x : α/φ) :
    factor.inv x * x = 1 := begin
    induction x, apply quot.sound,
    unfold left_mul, rw [mul_left_inv, mul_left_inv],
    apply is_subgroup.unit, trivial
  end

  instance factor.is_group {α : Type u} {φ : set α}
    [group α] [is_normal_subgroup φ] : group (α/φ) :=
  { mul := factor.mul,
    one := factor.one,
    mul_assoc := factor.assoc,
    one_mul := factor.one_mul,
    mul_one := factor.mul_one,
    inv := factor.inv,
    mul_left_inv := factor.left_inv }
end

def mul_uniq {α : Type u} {a b c d : α} [has_mul α] (h : a = b) (g : c = d) :
  a * c = b * d :=
begin induction h, induction g, reflexivity end

def homo_saves_unit {α : Type u} {β : Type v} [group α] [group β]
  (φ : α ⤳ β) : φ.val 1 = 1 := begin
  cases φ with φ H, apply square_is_unique, calc
    φ 1 * φ 1 = φ (1 * 1) : (H 1 1)⁻¹
          ... = φ 1 : φ # identity_sqr⁻¹
end

def homo_respects_inv {α : Type u} {β : Type v} [group α] [group β]
  (φ : α ⤳ β) (x : α) : φ.val x⁻¹ = (φ.val x)⁻¹ := begin
  cases φ with φ H, calc
    φ x⁻¹ = φ x⁻¹ * 1 : begin symmetry, apply monoid.mul_one end
      ... = φ x⁻¹ * (φ x * (φ x)⁻¹) :
            begin
              apply congr_arg, symmetry,
              apply mul_right_inv
            end
      ... = (φ x⁻¹ * φ x) * (φ x)⁻¹ : by symmetry; apply monoid.mul_assoc
      ... = φ (x⁻¹ * x) * (φ x)⁻¹ : (* (φ x)⁻¹) # (H x⁻¹ x)⁻¹
      ... = φ 1 * (φ x)⁻¹ :
            begin
              apply congr_arg (λ y, φ y * (φ x)⁻¹),
              apply group.mul_left_inv
            end
      ... = 1 * (φ x)⁻¹ : (* (φ x)⁻¹) # (homo_saves_unit ⟨φ, H⟩)
      ... = (φ x)⁻¹ : by apply monoid.one_mul
end

lemma homo_respects_div {α : Type u} {β : Type v} [group α] [group β]
  (φ : α ⤳ β) (x y : α) : φ.val (x / y) = φ.val x / φ.val y := begin
  cases φ with φ H, calc
    φ (x / y) = φ x * φ y⁻¹ : by apply H
          ... = φ x * (φ y)⁻¹ :
                begin apply congr_arg, apply homo_respects_inv ⟨φ, H⟩ end
          ... = φ x / φ y : by reflexivity
end

instance ker_is_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : α ⤳ β) : is_subgroup (ker φ) :=
{ unit := begin unfold ker, apply homo_saves_unit end,
  mul := begin
    intros a b h g,
    unfold ker at h, unfold ker at g,
    unfold ker, simp [set_of, has_mem.mem, set.mem],
    transitivity, apply φ.property, symmetry,
    transitivity, apply identity_sqr,
    apply mul_uniq, exact h⁻¹, exact g⁻¹
  end,
  inv := begin
    intros x h,
    unfold ker at h, unfold ker, cases φ with φ H, calc
      φ x⁻¹ = (φ x)⁻¹ : homo_respects_inv ⟨φ, H⟩ x
        ... = 1⁻¹     : group.inv # h
        ... = 1       : identity_inv⁻¹
  end }

instance ker_is_normal_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : α ⤳ β) : is_normal_subgroup (ker φ) := begin
  apply is_normal_subgroup.mk, intros n g h, cases φ with φ H,
  simp [ker, set_of, has_mem.mem, set.mem] at *,
  rw [H n g] at h,
  calc
    φ (g * n) = φ g * φ n : H g n
          ... = φ g * (φ g)⁻¹ : by rw [eq_inv_of_mul_eq_one h]
          ... = 1 : by apply mul_right_inv
end

instance im_is_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : α ⤳ β) : is_subgroup (im φ) :=
{ unit := ⟨1, homo_saves_unit φ⟩,
  mul := begin
    intros a b g h, unfold im at g, unfold im at h, unfold im,
    cases g with x g, cases h with y h,
    existsi (x * y), transitivity, apply φ.property,
    induction g, induction h, reflexivity
  end,
  inv := begin
    intros x h, unfold im at h, unfold im,
    cases h with y h, existsi y⁻¹,
    transitivity, apply homo_respects_inv,
    apply congr_arg, exact h
  end }

section
  variables {α : Type u} {β : Type v} [group α] [group β] {φ : α ⤳ β}

  def Im.mul (x y : Im φ) : Im φ := begin
    induction x with x h, induction y with y g,
    fapply subtype.mk, exact x * y,
    induction h with u h, induction g with v g,
    unfold im, existsi u * v,
    cases φ with φ H, simp [*] at *,
    rw [H u v, g, h]
  end

  instance : has_mul (Im φ) :=
  ⟨Im.mul⟩

  def Im.inv : Im φ → Im φ := begin
    intro x, induction x with x h,
    fapply subtype.mk, exact x⁻¹,
    induction h with n h, unfold im,
    existsi n⁻¹, rw [homo_respects_inv φ n, h]
  end

  instance : has_inv (Im φ) :=
  ⟨Im.inv⟩

  def Im.one : Im φ :=
  ⟨1, ⟨1, homo_saves_unit φ⟩⟩

  instance : has_one (Im φ) :=
  ⟨Im.one⟩

  theorem Im.mul_assoc (x y z : Im φ) : x * y * z = x * (y * z) := begin
    induction x with x h, induction y with y g, induction z with z f,
    apply subtype.eq, apply monoid.mul_assoc
  end

  theorem Im.mul_one (x : Im φ) : x * 1 = x :=
  begin induction x with x h, apply subtype.eq, apply monoid.mul_one end

  theorem Im.one_mul (x : Im φ) : 1 * x = x :=
  begin induction x with x h, apply subtype.eq, apply monoid.one_mul end

  theorem Im.mul_left_inv (x : Im φ) : x⁻¹ * x = 1 :=
  begin induction x with x h, apply subtype.eq, apply mul_left_inv end

  instance Im.is_group : group (Im φ) :=
  { mul := Im.mul,
    one := Im.one,
    mul_assoc := Im.mul_assoc,
    one_mul := Im.one_mul,
    mul_one := Im.mul_one,
    inv := Im.inv,
    mul_left_inv := Im.mul_left_inv }
end

lemma mul_left_inv_inv {α : Type u} [group α] (a b : α) :
  (b⁻¹ * a⁻¹) * (a * b) = 1 :=
by rw [←monoid.mul_assoc, monoid.mul_assoc b⁻¹, mul_left_inv, monoid.mul_one, mul_left_inv]

def ker.im {α : Type u} {β : Type v}
  [group α] [group β] {φ : α ⤳ β} : α/ker φ → Im φ := begin
  intro x, fapply @quot.hrec_on α (left_mul (ker φ)) _ x; clear x,
  { intro x, existsi φ.val x, existsi x, trivial },
  { intros a b h, apply heq_of_eq, apply subtype.eq,
    unfold subtype.val, transitivity, symmetry, apply inv_of_inv,
    apply inv_eq_of_mul_eq_one, rw [←homo_respects_inv φ a],
    transitivity, symmetry, apply φ.property, assumption }
end

theorem «Fundamental theorem on homomorphisms» {α : Type u} {β : Type v}
  [group α] [group β] {φ : α ⤳ β} : Im φ ≅ α/ker φ := begin
  split, tactic.swap,
  { intro x, cases x with x h,
    apply factor.incl, exact classical.some h },
  split,
  { intros a b,
    have p := classical.some_spec a.property,
    have q := classical.some_spec b.property,
    have r := classical.some_spec (a * b).property,
    cases a with a h, cases b with b g,
    cases h with u h, cases g with v g,
    apply quot.sound, simp [left_mul, has_mem.mem, set.mem, ker, set_of],
    cases φ with φ H, simp at *, rw [H, H, p, q],
    transitivity, apply congr_arg (λ x, x * (a * b)),
    transitivity, apply homo_respects_inv ⟨φ, H⟩,
    transitivity, apply has_inv.inv # r,
    apply inv_explode, apply mul_left_inv_inv },
  split; existsi ker.im; intros x,
  { induction x, apply quot.sound, unfold left_mul,
    simp [has_mem.mem, set.mem, ker, set_of],
    transitivity, apply φ.property,
    rw [homo_respects_inv], transitivity,
    apply congr_arg (λ y, y⁻¹ * φ.val x),
    have p := classical.some_spec (@ker.im._proof_1 _ _ _ _ φ x),
    exact p, apply mul_left_inv, trivial },
  { induction x with x h, apply subtype.eq,
    apply classical.some_spec h }
end

instance abelian_subgroups {α : Type u} [comm_group α]
  (φ : set α) [is_subgroup φ] : is_normal_subgroup φ := begin
  apply is_normal_subgroup.mk, intros g h H,
  rw [comm_group.mul_comm], assumption
end

def tower {α : Type u} [group α] (a : α) :=
{ b // ∃ (n : ℤ), b = a^n }

def cyclic {α : Type u} [group α] (a : α) :=
group (tower a)