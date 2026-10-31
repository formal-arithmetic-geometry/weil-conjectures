/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumScalarRepresentative
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumScalarRepresentative

/-! # Unbounded representative equation for the exact derived sum scalar isomorphism

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-scalar-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor upperStar lowerStar openImmersionLowerShriek
  etaleLowerShriek ProEtale.etaleSheafExtendScalars

/-- Unbounded representative equation for the exact derived sum scalar isomorphism.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-scalar-representative).

Proof: Identify the published exact-derived sum coefficient map with the conjugate of the exact
complex scalar square.
Use the exact map-derived comparison to transport the sheaf-level summation/scalar equation
through localization. Functoriality of the derived comparisons proves the displayed representative
equation on every complex. -/
theorem ordinaryChartSumScalarRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (e : X ⟶ Y) [Etale e]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    :
    let σ :
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
            scalarExtension φ Y ≅
          scalarExtension φ X ⋙
            (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory :=
      ((conjugateIsoEquiv
        ((etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction.comp
          (Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology φ)))
        ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ)).comp
          (etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction)).symm
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIsoSheaf φ e))).symm
    (scalarExtension φ Y).map
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.hom.app
          P) ≫
      scalarExtensionRepresentative φ Y
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (etaleSumScalarComplexMap φ e P) =
    σ.hom.app (DerivedCategory.Q.obj P) ≫
      (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
        (scalarExtensionRepresentative φ X P) ≫
      (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryFactors.hom.app
        (coefficientExtendedComplex φ X P) := by
  have h := exactSumScalarComparison
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ Y)
    (LX := scalarExtension φ X) (LY := scalarExtension φ Y)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
    (upperStarRestrictScalarsIsoSheaf φ e) P
  simpa only [scalarExtensionRepresentative,
    etaleSumScalarSheafIso, etaleSumScalarComplexMap, coefficientExtendedComplex,
    scalarExtension, ProEtale.pbcFixedScalarExtension, Sheaf.restrictScalars,
    Iso.symm_hom, Functor.comp_obj] using h

end AlgebraicGeometry.Etale
