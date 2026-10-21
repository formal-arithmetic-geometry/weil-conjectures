# AlgebraicGeometry.ProEtale.CondensedRing.ClosedSupportConstructibleAssertions

## Reason

Repair the returned delivery against the current live module, as requested by the
landing return for head 18886166d. The file is now present and already has the
relocated Serre triangulatedness import and complete zero-hole proofs. Preserve
those changes rather than treating the module as absent.

The live assertion quantifies both finite-colimit preservation of the closed direct
image and an adjunction having that functor as left adjoint. The second already
implies the first by `a.leftAdjoint_preservesColimits`. Derive this prerequisite
locally before forming the termwise derived functor, removing the redundant
independent witness. This is the retained substantive definition repair, reapplied
to the current source, rather than an unchanged restoration or rebase.

The old and new assertions are equivalent: from the old assertion retain its
adjunction; from the new assertion supply the finite-colimit-preservation witness
induced by that adjunction. All preservation instances are proofs, so proof
irrelevance identifies the derived functors and their arrows. The normalization,
the distinguished triangle, all four constructibility clauses and both coefficient
choices are identical. This applies also to empty schemes, zero complexes, and the
identity closed immersion. There is no added hypothesis or arbitrary data choice.

## Old

Current live definition, verbatim:

```lean
def ClosedSupportConstructibleAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] : Prop :=
  ∃ (_ : PreservesFiniteColimits (lowerStar Λ i)) (a : lowerStar Λ i ⊣ formalClosedSupport Λ i j),
    (∀ M : FormalSupportModules Λ X,
      (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
        (formalSupportKernelInclusion Λ j).app M) ∧
    ∀ K : BoundedConstructible (condensedRingObj Λ X),
      ∃ δ : (lowerStar Λ j).rightDerivedFunctor.obj
          ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj) ⟶
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧,
        Triangle.mk
            (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj)
            ((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
              K.obj) δ ∈ distTriang _ ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ j).rightDerivedFunctor.obj
            ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          (((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧) ∧
        boundedConstructible (condensedRingObj Λ Z)
          ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)
```

## New

```lean
def ClosedSupportConstructibleAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] : Prop :=
  ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
    letI := a.leftAdjoint_preservesColimits
    (∀ M : FormalSupportModules Λ X,
      (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
        (formalSupportKernelInclusion Λ j).app M) ∧
    ∀ K : BoundedConstructible (condensedRingObj Λ X),
      ∃ δ : (lowerStar Λ j).rightDerivedFunctor.obj
          ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj) ⟶
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧,
        Triangle.mk
            (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj)
            ((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
              K.obj) δ ∈ distTriang _ ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ j).rightDerivedFunctor.obj
            ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          (((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧) ∧
        boundedConstructible (condensedRingObj Λ Z)
          ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)
```

The constructor in `support_constructible_of_localization` now supplies the
adjunction directly. All public imports, theorem signatures, completed arguments,
and local elaboration attributes are preserved. No target statement changes.
The meaning of the definition is equivalent, so no semantic target review is reopened.

## Users

The current `tools/downstream.py --uses` check lists 74 downstream modules but no
external use of the predicate. Whole-word searches of lean/ and quarantine/ also
find no external use of either public declaration. The two direct importers,
ClosedAdjointConstructibleYoneda and RestrictionLocal, are present in quarantine/
and do not reference the predicate. No consumer adaptation is needed. The table
lists every module from the downstream check, with current claim holders.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedSupportConstructible | Q9 | Derive the preservation instance from the adjunction; adapt the constructor proof. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| TargetsCheck | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No declaration reference; meaning unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No declaration reference; meaning unchanged; no adaptation. |

## Status

landed 20261021T203722-L-3858705 2026-10-21 (merge of deliver/Q9/Sheaf.Paper.ClosedSupportConstructible)
