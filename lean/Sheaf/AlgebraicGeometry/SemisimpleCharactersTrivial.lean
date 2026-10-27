module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes

/-! # Characters of semisimple algebraic groups

Source: Milne, Algebraic Groups, Corollary 21.50 and Definition 12.45,
via Proposition 6.18 and Corollary 6.19(d)
(blueprint: lem-sfb-semisimple-characters-trivial).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every character of a semisimple group is the identity-valued morphism. This is equality
of scheme morphisms, hence it remains an equality after every scalar extension, including
nonreduced test algebras. The one on the right is the constant identity section, whereas
addition in the character group is multiplication of values.

Source: Milne, Algebraic Groups, Corollary 21.50, Definition 12.45, Corollary 6.19(d)
(blueprint: lem-sfb-semisimple-characters-trivial).

Proof: `lem-sfb-semisimple-group-perfect` (`semisimpleGroupScheme_perfect`) gives Hder = H
for the given smooth connected semisimple affine algebraic group. The target G_m is
commutative and affine, with Laurent coordinate ring and comultiplication t ↦ t ⊗ t
(`def-sc-gm-ga`). By `lem-sfb-smooth-connected-derived-subgroup`, the character is trivial
on Hder. Substitution of Hder = H proves the equality of morphisms. Pulling back that
equality along any scalar extension gives the same identity-valued character there,
including on every test algebra. The identity-valued character itself exists, so the
character group has exactly its zero character. -/
theorem semisimpleGroupScheme_characters_trivial {k : Type u} [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H] (hH : IsSemisimpleGroupScheme H)
    (χ : H ⟶ StandardGroupSchemes.multiplicative k) [IsMonHom χ] :
    χ = 1 := by
  sorry

end AlgebraicGeometry
