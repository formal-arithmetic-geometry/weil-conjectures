/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.FieldExtensionIntegralComparisons
public import Sheaf.Paper.FieldScalarNormalizedSystems

/-! # FieldExtensionLimitEquations

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-limit-equations).

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

/-- The comparisons on integral objects are exactly the reconstructed total limits
of the original strict derived-tower arrows. Source: clause (2), derived limits
(blueprint: def-sp-field-extension-limit-equations). -/
structure LimitEquations (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (i : IntegralComparison P D j p d E F h mE mF) : Prop where
  left : ∀ M : Integral P E X,
    (i.comparison.left.hom.app M).hom =
      (mF.realization.reconstructionY _).hom ≫
        (SpIntegralAdjunction.limit P.coefficients.l F.val Y ((D.coordinates F).abelian Y)
          mF.reductionY mF.normalizationY).map
            ((i.scalarReductionY.hom.app ((support P D j p d mE).obj M) ≫
              i.towers.scalarY.map (mE.realization.leftComparison.hom.app M) ≫
              i.towers.comparison.left.hom.app ((reduceX P D j p d mE).obj M) ≫
              (SpTowerGluing.support P.coefficients.l F.val (D.base F) (D.operations F)
                (D.coordinates F) (SpTowerGamma.factorization j p) mF.supportClosed).map
                  (i.scalarReductionX.inv.app M) ≫
              mF.realization.leftComparison.inv.app ((scalar P h X).obj M)).hom) ≫
        (mF.realization.reconstructionY _).inv
  right : ∀ K : Integral P E Y,
    (i.comparison.right.hom.app K).hom =
      (mF.realization.reconstructionX _).hom ≫
        (SpIntegralAdjunction.limit P.coefficients.l F.val X ((D.coordinates F).abelian X)
          mF.reductionX mF.normalizationX).map
            ((i.scalarReductionX.hom.app ((exceptional P D j p d mE).obj K) ≫
              i.towers.scalarX.map (mE.realization.rightComparison.hom.app K) ≫
              i.towers.comparison.right.hom.app ((reduceY P D j p d mE).obj K) ≫
              mF.exceptional.map (i.scalarReductionY.inv.app K) ≫
              mF.realization.rightComparison.inv.app ((scalar P h Y).obj K)).hom) ≫
        (mF.realization.reconstructionX _).inv

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
