# AlgebraicGeometry.Etale.acyclicFlatProperCoefficientModel proof context

## Reason

Server preflight requests this record because new section `variable` commands and
local `attribute` commands conservatively count as changes to the elaboration
interface. They support proved private comparison and mate lemmas and control
unnecessary unfolding of chosen derived adjoints. No public definition, signature,
public import, universe binder, generated declaration or exported attribute changes.
No source-library module is edited. There are no new proof holes.

## Old

The original module has this exact initial elaboration environment:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale
```

That environment and all nine existing public declarations are retained. The
original theorem signature, verbatim, is:

```lean
theorem acyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {W V : Scheme.{u}} (r : W ⟶ V) [IsProper r] [IsNoetherian W] [IsNoetherian V]
    (φ : A →+* B)
    (C : CochainComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : IsAcyclicFlatProperCoefficientModel φ r C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ∧
      IsIso (properAcyclicComparison A r C) ∧
      IsIso (properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      IsIso (scalarExtensionRepresentative φ W C) ∧
      IsIso (scalarExtensionRepresentative φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ((properCoefficientTensor φ V).map (properAcyclicComparison A r C) ≫
          (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
            (scalarExtensionRepresentative φ W C) =
        scalarExtensionRepresentative φ V
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map (properCoefficientComplexMap φ r C) ≫
          properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      (∀ (C' : CochainComplex
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (_hC' : IsAcyclicFlatProperCoefficientModel φ r C') (h : C ⟶ C'),
        (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              ((properCoefficientTensor φ W).map (DerivedCategory.Q.map h)) =
          (properCoefficientTensor φ V).map
              ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
                (DerivedCategory.Q.map h)) ≫
            (properCoefficientMap φ r).app (DerivedCategory.Q.obj C') ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properAcyclicComparison A r C' =
          properAcyclicComparison A r C ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ≫
            properAcyclicComparison B r (coefficientExtendedComplex φ W C') =
          properAcyclicComparison B r (coefficientExtendedComplex φ W C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              (DerivedCategory.Q.map
                (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ∧
        (properCoefficientTensor φ W).map (DerivedCategory.Q.map h) ≫
            scalarExtensionRepresentative φ W C' =
          scalarExtensionRepresentative φ W C ≫ DerivedCategory.Q.map
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h) ∧
        (properCoefficientTensor φ V).map (DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ≫
            scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C') =
          scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
            DerivedCategory.Q.map
              (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
                (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ∧
        ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properCoefficientComplexMap φ r C' =
          properCoefficientComplexMap φ r C ≫
            ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h))
```

Its old proof is `by sorry`. There were no generic proof sections, cached local
instances or local transparency attributes between the public definitions and it.

## New

The same public theorem signature is retained verbatim and its proof is complete.
All preceding public definitions and abbreviations retain their literal signatures
and bodies. The existing seven public imports are unchanged. The only new proof
import is private:

```lean
import all Sheaf.Paper.WitnessCompatibility
```

It exposes the existing proved private preservation and unit-normalization results
for this proof, and reexports no private declarations to consumers.

The new `ProofCalculations` section contains only private declarations. Its
`CachedInstances`, `DerivedComparison` and `ScalarRepresentativeComparison` sections
scope the generic variables below; each is closed before the public theorem.
The eleven cached instances are private abbreviations for existing proof-valued
instances, activated only locally inside `ProofCalculations`.

These are the added local proof-context commands, in file order:

```lean
variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

attribute [local instance] cachedPreadditive cachedCoproducts cachedColimits
  cachedFlatResolution cachedInjectiveResolution cachedExactColimits cachedTensor4
  cachedTensor12 cachedTensor23 cachedTensorLeft cachedTensorRight

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions E]
  {F : D ⥤ E} {G : E ⥤ D} [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]

variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions E]
  {F : D ⥤ E} {G : E ⥤ D} [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]

attribute [local irreducible] Functor.mapHomotopyCategoryFactors
  Functor.mapDerivedCategoryFactors DerivedCategory.Qh
  Functor.rightDerivedFunctorUnit Functor.leftDerivedFunctorCounit
  Adjunction.ofIsRightAdjoint Adjunction.homEquiv
  ProEtale.etaleSheafExtendScalarsAdjunction upperStarLowerStarAdjunction
  Adjunction.derivedAdjunction

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  scalarExtensionRepresentative scalarGeometricRepresentative properAcyclicComparison

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Functor.mapHomotopyCategoryFactors
  Functor.mapDerivedCategoryFactors Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctorCounit Adjunction.ofIsRightAdjoint Adjunction.homEquiv
  ProEtale.etaleSheafExtendScalarsAdjunction upperStarLowerStarAdjunction
  Adjunction.derivedAdjunction

attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.ofIsGrothendieckAbelian ProEtale.etaleSheafExtendScalars
  mateEquiv scalarPullbackIso derivedUpperStarLowerStarAdjunction
  Adjunction.mapHomologicalComplex
  MorphismProperty.kFlat HomologicalComplex.quasiIso

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types true
```

All reducibility and instance attributes have the `local` modifier. The transparency
options affect elaboration in this module, not imported declarations or kernel
checking. The final proof uses explicit component and normalization lemmas while
keeping chosen functors folded. There is no change to compiler limits, heartbeat
limits, kernel checks, notation or exported instances. Diagnostic options are absent.

## Users

`tools/downstream.py` reports 57 transitive consumers. Searching all nine existing
public declaration names with its `--uses` option finds only the item itself: the
consumers import the unchanged interface without textual references to those names.
The unchanged public definitions and theorem signature were compared literally
against the shared source. Their statements and meanings do not change, and none
can refer to the new private helper declarations or inherit these local attributes.
This is a source/interface check, not a downstream rebuild. The delivered file
compiles through `lcompile.py`; no consumer needs adaptation and no other group's
file is included. No target statement re-review is needed for a definition change,
because no target-used definition changes. Holder labels use the current claim
records and configured expiry; no claim is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | J3 | Completed proof; original public API retained. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Public API and statement meaning unchanged; no adaptation. |

## Status

landed 20261021T061350-L-1764762 2026-10-21 (merge of deliver/J3/Sheaf.Paper.AcyclicFlatProperCoefficientModel)
