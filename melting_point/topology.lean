import melting_point.set
open melting_point.set

meta def tactic.interactive.enumeration : tactic unit :=
`[ repeat { { apply or.inl, trivial } <|> apply or.inr } ]

meta def tactic.interactive.sinduction
  (q : interactive.parse interactive.types.texpr) : tactic unit := do
  tactic.repeat (do
    -- ???
    tactic.i_to_expr q >>= tactic.induction,
    tactic.i_to_expr q >>= tactic.rewrite_target,
    tactic.i_to_expr q >>= tactic.clear,
    tactic.swap),
  tactic.i_to_expr q >>= tactic.induction,
  pure ()

meta def calcset : tactic unit := `[
  { funext x, induction x; apply propext; split; intro h;
     try { { left, trivial <|> { enumeration, done } } <|>
           { right, trivial <|> { enumeration, done } } <|>
           { split; assumption } <|>
           { enumeration, done } },
     repeat { cases h, try
       { { repeat { cases h_left }, done } <|>
         { repeat { cases h_right }, done } } },
     repeat { split; { trivial <|> enumeration } } }
]

meta def findset : tactic unit :=
`[ repeat { { apply or.inl, calcset, done } <|> apply or.inr } ]

namespace melting_point.topology
universe u

structure topology (α : Type u) :=
(is_open : set (set α))
(empty_open : is_open ∅)
(full_open : is_open set.univ)
(inter_open : Π u v, is_open u → is_open v → is_open (u ∩ v))
(union_open : Π u v, is_open u → is_open v → is_open (u ∪ v))

def discrete (α : Type u) : topology α := begin
  fapply topology.mk, exact set.univ,
  repeat { intros, trivial }
end

def trivial.open (α : Type u) : set (set α) :=
{ ∅, set.univ }

def trivial (α : Type u) : topology α := begin
  fapply topology.mk, exact trivial.open α,
  { apply or.inr, apply or.inl, trivial },
  { apply or.inl, trivial },
  { intros u v a b,
    sinduction a; rw [inter.comm],
    { rw [inter.empty], enumeration },
    { rw [inter.univ], assumption } },
  { intros u v a b,
    sinduction a; rw [union.comm],
    { rw [union.empty], assumption },
    { rw [union.univ], enumeration } }
end

end melting_point.topology