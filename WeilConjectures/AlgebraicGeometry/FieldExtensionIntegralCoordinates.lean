/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralComparisons
public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedSystems

/-! # FieldExtensionIntegralCoordinates

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-integral-coordinates).

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

/-- Exact restriction from completed modules to the recorded section-ring presentation.
Source: completed coefficient identification in clause (1)
(blueprint: def-sp-field-extension-integral-coordinates). -/
abbrev restriction (E : FieldShriekSystem.Index P) (T : Scheme.{u})
    (R : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T)) :=
  SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)

/-- Canonical completed/section-ring scalar coordinates, fixed on ordinary tensors
and by derived counits. Source: clause (1)
(blueprint: def-sp-field-extension-integral-coordinates). -/
structure IntegralCoordinates (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)) where
  data : FieldScalar.ScalarData P.coefficients.l E.val F.val (IntermediateField.inclusion h)
    T ((D.coordinates E).abelian T) ((D.coordinates F).abelian T) RA RB
  coefficient : data.coefficients.integral = RA.coefficient.hom ≫
    WeilConjectures.completedCoefficientMap P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T ≫
      RB.coefficient.inv
  integralOrdinary : completedOrdinaryScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T ⋙
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            RB.coefficient.hom)) ≅
    (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        RA.coefficient.hom)) ⋙ (FieldScalar.integralScalar data.coefficients).model.E
  integralOrdinary_sections : ∀ (M : scalarReductionSource P.coefficients.l E.val T)
    (U : T.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted P.coefficients.l F.val T).obj.obj U)
    (x : M.val.obj U),
    (integralOrdinary.hom.app M).val.app U
      (completedScalarTensorSection P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T M U s x) =
      SheafOfModules.systemModelTmul
        (FieldScalar.integralScalar data.coefficients).model _ U
        (RB.coefficient.inv.hom.app U s) x
  ordinaryDerived : completedDerivedScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T ⋙ (restriction P D F T RB).mapDerivedCategory ≅
    (restriction P D E T RA).mapDerivedCategory ⋙
      (FieldScalar.integralScalar data.coefficients).model.T
  ordinaryDerived_rep : ∀ Q : CochainComplex (scalarReductionSource P.coefficients.l E.val T) ℤ,
    ordinaryDerived.hom.app (DerivedCategory.Q.obj Q) ≫
        (FieldScalar.integralScalar data.coefficients).model.T.map
          ((restriction P D E T RA).mapDerivedCategoryFactors.hom.app Q) ≫
        (FieldScalar.integralScalar data.coefficients).model.ε.app
          (((restriction P D E T RA).mapHomologicalComplex (.up ℤ)).obj Q) =
      (restriction P D F T RB).mapDerivedCategory.map
        (completedScalarCounit P.coefficients.l E.val F.val (IntermediateField.inclusion h)
          T Q) ≫
        (restriction P D F T RB).mapDerivedCategoryFactors.hom.app
          ((completedOrdinaryScalarComplex P.coefficients.l E.val F.val
            (IntermediateField.inclusion h) T).obj Q) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex integralOrdinary.hom
          (.up ℤ)).app Q)
end AlgebraicGeometry.ProEtale.FieldExtensionTowers
