/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralModels

/-! # FieldExtensionStrictLimits

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-strict-limits).

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

/-- Finite-free extension commutes with the total right derived limit of arbitrary strict
completed-coefficient towers. The normalization is the ordinary limit/tensor map on
K-injective representatives, so the comparison is not an arbitrary isomorphism.
Source: clause (1) (blueprint: def-sp-field-extension-strict-limits). -/
structure StrictLimitComparison (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (T : Scheme.{u}) where
  [exactLimits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T)]
  [exactColimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T)]
  [towerLimits : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T))]
  [towerColimits : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T))]
  kinjective : ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ℤ,
    I.IsKInjective →
    CochainComplex.IsKInjective ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T)).mapHomologicalComplex
              (.up ℤ)).obj I)
  chain : ∀ I : CochainComplex
      (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ℤ,
    ((completedOrdinaryScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T).mapHomologicalComplex
          (.up ℤ)).obj
        (((lim :
            (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ⥤ _).mapHomologicalComplex
              (.up ℤ)).obj I) ≅
      ((lim :
          (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l F.val T) ⥤ _).mapHomologicalComplex
          (.up ℤ)).obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
              (IntermediateField.inclusion h) T)).mapHomologicalComplex
              (.up ℤ)).obj I)
  chain_projection : ∀ (I : CochainComplex
      (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ℤ) (i : ℤ) (n : ℕ),
    ((chain I).hom.f i) ≫ limit.π
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
            (IntermediateField.inclusion h) T)).obj (I.X i)) (op n) =
      (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T).map (limit.π (I.X i) (op n))
  iso : coefficientConstantTowerLimit P.coefficients.l E.val T ⋙
      completedDerivedScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T ≅
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T)).mapDerivedCategory ⋙
      coefficientConstantTowerLimit P.coefficients.l F.val T
  normalized : ∀ (I : CochainComplex
      (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T)).mapHomologicalComplex
              (.up ℤ)).obj I)],
    iso.hom.app (DerivedCategory.Q.obj I) ≫
        (coefficientConstantTowerLimit P.coefficients.l F.val T).map
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
              (IntermediateField.inclusion h) T)).mapDerivedCategoryFactors.hom.app I) =
      (completedDerivedScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T).map
          ((lim :
            (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ⥤ _).rightDerivedFunctorObjQIso
              I).hom ≫
        completedScalarCounit P.coefficients.l E.val F.val (IntermediateField.inclusion h)
          T (((lim :
            (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l E.val T) ⥤ _).mapHomologicalComplex
              (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map (chain I).hom ≫
        ((lim :
          (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l F.val T) ⥤ _).rightDerivedFunctorObjQIso
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
              (completedOrdinaryScalarExtension P.coefficients.l E.val F.val
                (IntermediateField.inclusion h) T)).mapHomologicalComplex
              (.up ℤ)).obj I)).inv

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
