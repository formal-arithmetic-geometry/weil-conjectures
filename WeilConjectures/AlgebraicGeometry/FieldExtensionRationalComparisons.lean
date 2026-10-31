/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionRationalModels

/-! # FieldExtensionRationalComparisons

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-rational-comparisons).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- The rational comparisons are the integral comparisons tensored with one, including
units, counits and the localized purity square. Source: clause (3)
(blueprint: def-sp-field-extension-rational-comparisons). -/
structure RationalComparison (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (i : IntegralComparison P D j p d E F h mE mF)
    (rE : RationalModel P D j p d E mE) (rF : RationalModel P D j p d F mF) where
  comparison : FieldScalarAdjunctionComparison rE.adjunction rF.adjunction
    (rationalScalar P h X) (rationalScalar P h Y)
  left : ∀ M : Integral P E X,
    HEq (comparison.left.hom.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val X).obj M))
      ((sfRationalConstructibleLocalization P.coefficients.l F.val Y).map
        (i.comparison.left.hom.app M))
  right : ∀ K : Integral P E Y,
    HEq (comparison.right.hom.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val Y).obj K))
      ((sfRationalConstructibleLocalization P.coefficients.l F.val X).map
        (i.comparison.right.hom.app K))
  source : rE.source.functor ⋙ rationalScalar P h X ≅
    rationalScalar P h Y ⋙ rF.source.functor
  source_localized : ∀ K : Integral P E Y,
    HEq (source.hom.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val Y).obj K))
      ((sfRationalConstructibleLocalization P.coefficients.l F.val X).map
        (i.sourceComparison.hom.app K))
  purity : ∀ K : Rational P E Y,
    (rationalScalar P h X).map (rE.gamma.hom.app K) ≫ comparison.right.hom.app K =
      source.hom.app K ≫ rF.gamma.hom.app ((rationalScalar P h Y).obj K)

/-- The second displayed rational comparison on the actual published pullback,
signed twist and shift functors, obtained by the two source identifications.
Source: clause (3) (blueprint: def-sp-field-extension-rational-comparisons). -/
def rationalPullbackComparison (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (i : IntegralComparison P D j p d E F h mE mF)
    (rE : RationalModel P D j p d E mE) (rF : RationalModel P D j p d F mF)
    (r : RationalComparison P D j p d E F h mE mF i rE rF) :
    rationalPuritySource P j p d E ⋙ rationalScalar P h X ≅
      rationalScalar P h Y ⋙ rationalPuritySource P j p d F :=
  Functor.isoWhiskerRight rE.sourceIdentification.symm _ ≪≫ r.source ≪≫
    Functor.isoWhiskerLeft _ rF.sourceIdentification

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
