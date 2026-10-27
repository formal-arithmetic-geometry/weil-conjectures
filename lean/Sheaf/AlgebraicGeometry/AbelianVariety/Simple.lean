module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-! # Simple abelian varieties over the ground field

Source: Milne, Abelian Varieties, Chapter I, §10, printed p.42, before Proposition 10.1.
(blueprint: def-sfb-simple-abelian-variety)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An abelian variety is simple over its ground field if it has positive dimension and
no closed abelian subgroup over that field of strictly intermediate dimension.

Source: Milne, Abelian Varieties, Chapter I, §10, printed p.42, before Proposition 10.1.
(blueprint: def-sfb-simple-abelian-variety)

The quantification is over closed subgroup schemes, rather than subgroups of rational
points or subvarieties after extending the field. No perfectness assumption is made. -/
def IsSimpleAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [GrpObj C] [IsAbelianVariety C] : Prop :=
  0 < IsAbelianVariety.dim C ∧
    ∀ (B : Over (Spec (.of k))) [GrpObj B] [IsAbelianVariety B]
      (i : B ⟶ C) [IsMonHom i] [IsClosedImmersion i.left],
      ¬ (0 < IsAbelianVariety.dim B ∧ IsAbelianVariety.dim B < IsAbelianVariety.dim C)

end AlgebraicGeometry
