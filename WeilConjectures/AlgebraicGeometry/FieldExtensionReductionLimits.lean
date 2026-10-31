/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionSystemCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedSystems

/-! # FieldExtensionReductionLimits

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-reduction-limits).

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

/-- Whole-system reduction identity using the canonical integral and system scalar
coordinates. Source: clause (1)
(blueprint: def-sp-field-extension-reduction-limits). -/
structure Reduction (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)) where
  coordinates : IntegralCoordinates P D E F h T RA RB
  systems : SystemCoordinates P D E F h T RA RB coordinates
  integral : (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
    integralScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T ⋙
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            RB.coefficient.hom)).mapDerivedCategory ≅
    (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
      (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        RA.coefficient.hom)).mapDerivedCategory ⋙
          (FieldScalar.integralScalar coordinates.data.coefficients).model.T
  integral_normalized : ∀ K : Integral P E T,
    (restriction P D F T RB).mapDerivedCategory.map
        ((completedScalarComparison P.coefficients.l E.val F.val
          (IntermediateField.inclusion h) T).app K.obj) ≫ integral.hom.app K =
      coordinates.ordinaryDerived.hom.app K.obj
  reduction : (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
      integralScalarExtension P.coefficients.l E.val F.val (IntermediateField.inclusion h) T ⋙
        spCompletedReduction P.coefficients.l F.val T ((D.coordinates F).abelian T) RB ≅
    (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
      spCompletedReduction P.coefficients.l E.val T ((D.coordinates E).abelian T) RA ⋙
        towerScalar P D h T
  reduction_normalized : ∀ K : Integral P E T,
    reduction.hom.app K =
      RB.red.map (integral.hom.app K) ≫
        coordinates.data.comparison.isoDerived.hom.app
          ((restriction P D E T RA).mapDerivedCategory.obj K.obj) ≫
        systems.system.hom.app
          (RA.red.obj ((restriction P D E T RA).mapDerivedCategory.obj K.obj))

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
