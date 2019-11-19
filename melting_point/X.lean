import melting_point.topology
open melting_point.topology

inductive X
| a | b | c | d

namespace X
  def τ : set (set X) :=
  { { a },
    { c },
    { a, c },
    { a, b, c },
    { a, d, c },
    ∅, set.univ }

  example : topology X := begin
    fapply topology.mk, exact τ, enumeration,
    repeat { intros x y u v, sinduction u; sinduction v; findset }
  end
end X