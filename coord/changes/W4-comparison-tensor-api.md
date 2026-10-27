# AlgebraicGeometry.ProEtale.comparison_tensor_compatible

## Reason

Repair the returned duplicate-proof packet by reusing the existing proved helpers
of `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` (currently unclaimed).
An ordinary import cannot access its private constants. Expose the concrete
comparison API in place, remove the copies from the assigned item, and retain
the generic transport proof privately in its existing owner. The construction
`CategoryTheory.tensorTransport` is exposed because the public tensor comparison
definition uses it. No theorem statement, target meaning or construction changes.

## Old

The complete old definition bodies and theorem signatures are:

```lean
private def tensorTransport
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U) :
    (postcompose₂.obj G).obj T ≅ (((whiskeringLeft₂ D).obj G).obj G).obj U :=
  (postcompose₂.mapIso e.symm).app T ≪≫ m ≪≫
    ((((whiskeringLeft₂ D).obj F).mapIso e).app U) ≪≫
    (((whiskeringLeft₂ D).mapIso e).app G).app U

private noncomputable def comparisonTensorNatIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :=
  tensorTransport (Etale.derivedTensor (ModuleCat.{u + 1} Λ) X)
    (derivedTensor (ModuleCat.{u + 1} Λ) X)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedFunctorIsoMapDerivedCategory
    (asIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedTensorComparison)

private lemma supportComparison_eq (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm

private lemma comparison_tensor_compatible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Adjunction.ComparisonCompatible (comparisonOpenDerivedPullbackIso Λ j).symm
      (Etale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
      (comparisonTensorNatIso Λ U) (comparisonTensorNatIso Λ X)

private lemma comparison_tensor_app (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) (K : Etale.DerivedCategoryModule Λ X) :
    (comparisonTensorNatIso Λ X).app K =
      derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) K
```

The owning module imports ProjectionMapCompat privately; ComparisonCompatible
was previously used only in private signatures.

## New

The complete new definition bodies and theorem signatures are:

```lean
def tensorTransport
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U) :
    (postcompose₂.obj G).obj T ≅ (((whiskeringLeft₂ D).obj G).obj G).obj U :=
  (postcompose₂.mapIso e.symm).app T ≪≫ m ≪≫
    ((((whiskeringLeft₂ D).obj F).mapIso e).app U) ≪≫
    (((whiskeringLeft₂ D).mapIso e).app G).app U

noncomputable def comparisonTensorNatIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :=
  tensorTransport (Etale.derivedTensor (ModuleCat.{u + 1} Λ) X)
    (derivedTensor (ModuleCat.{u + 1} Λ) X)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedFunctorIsoMapDerivedCategory
    (asIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedTensorComparison)

lemma supportComparison_eq (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm

lemma comparison_tensor_compatible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Adjunction.ComparisonCompatible (comparisonOpenDerivedPullbackIso Λ j).symm
      (Etale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
      (comparisonTensorNatIso Λ U) (comparisonTensorNatIso Λ X)

lemma comparison_tensor_app (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) (K : Etale.DerivedCategoryModule Λ X) :
    (comparisonTensorNatIso Λ X).app K =
      derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) K
```

Only `private` is removed: all binders and bodies are identical. Keep all existing
public imports and declarations. Add
`public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate`,
the owner of the predicate now appearing in a public theorem signature.
The two public definitions remain the exact explicit composites they were before;
no arbitrary witness or proof hole is introduced.

The assigned module removes its copies of both definitions and all six duplicate
transport/coherence lemmas listed in the return. It imports the owner already
through its unchanged public import and uses the published concrete API.

## Users

The table includes every downstream module reported by tools/downstream.py.
This is an additive visibility change only. Every preexisting public signature
and body in the owning module is identical; old consumers therefore keep exactly
the same propositions and functors. Public names are qualified in CategoryTheory
or AlgebraicGeometry.ProEtale, and no existing public library name collides.
Only the assigned item's proof changes. No forced adaptation is claimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | Its supportComparison_eq reference now resolves through the public API; no edit. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale | W4 | Uses the published helpers; duplicate local proofs removed. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ProEtaleOpenResidueTorBound | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No old public signature or construction changes; no adaptation. |
| Sheaf.SixFunctors.ComparisonOpenTensorCoherence | unclaimed | Five helpers exposed in place; same types, bodies and existing public API. |

## Status

landed 20261024T191554-L-435036 2026-10-24 (merge of deliver/W4/Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale)
