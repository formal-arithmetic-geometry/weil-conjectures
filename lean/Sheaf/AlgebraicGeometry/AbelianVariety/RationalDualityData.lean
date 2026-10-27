module

public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalHom

/-! # Specified dual abelian varieties and pullback classification

Source: Milne, Abelian Varieties, I §8, pp.36–40, and §9 opening, p.41.
(blueprint: def-sfb-abelian-rational-duality-data)

## Main definitions

- `AbelianVarietyWithDual`: an abelian variety with a supplied normalized dual datum.
- `AbelianVarietyWithDual.dualHomClassifies`: the Poincare pullback characterization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- An abelian variety with specified dual Poincare datum; this selects no existence witness.
Source: Milne AV I §§8–9, pp.36–41
(blueprint: def-sfb-abelian-rational-duality-data). -/
structure AbelianVarietyWithDual (k : Type u) [Field k] where
  variety : Over (Spec (.of k))
  group : GrpObj variety
  abelian : IsAbelianVariety variety
  datum : AbelianDualPoincareDatum variety

attribute [instance] AbelianVarietyWithDual.group AbelianVarietyWithDual.abelian

/-- The dual homomorphism is characterized by pullback of the specified universal family.
Source: Milne AV I §9, p.41 (blueprint: def-sfb-abelian-rational-duality-data). -/
def AbelianVarietyWithDual.dualHomClassifies {k : Type u} [Field k]
    (A B : AbelianVarietyWithDual k)
    (f : abelianHom A.variety B.variety)
    (g : abelianHom B.datum.dual A.datum.dual) : Prop :=
  Nonempty
    ((Scheme.Modules.pullback (f.toMul.hom.hom ▷ B.datum.dual).left).obj B.datum.poincare ≅
      (Scheme.Modules.pullback (A.variety ◁ g.toMul.hom.hom).left).obj A.datum.poincare)

end AlgebraicGeometry
