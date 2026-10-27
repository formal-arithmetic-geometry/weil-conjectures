# Algebra.projective_of_geometricallyIntegral_fibres

## Reason

The completed proof compares scalar actions over a ring and its canonical universe lift.
Lean's alternative ULift scalar-action instances cause an instance diamond when forming
the tensor algebra equivalence. Disable these instances only while elaborating the theorem,
and permit backward definitional equality to reduce the chosen algebra actions. The
explicit scalar-action equalities then establish both tensor compatibilities.

The static interface checker classifies the scoped `attribute ... in` command as an
interface change. Its actual scope is this one theorem: the public signature, attributes,
public imports and instance environment seen by importers remain identical. This record
makes that elaboration choice available for independent review. Removing the scoped
commands fails to synthesize `Semiring (B' ⊗[R'] K)` and
`CompatibleSMul R R' B' K` at the algebra tensor equivalence.

## Old

```lean
theorem projective_of_geometricallyIntegral_fibres
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (hflat : RingHom.Flat (algebraMap R B))
    (hfibres : ∀ (p : Spec (.of R)) (K : Type (max u v w)) [Field K] [Algebra R K]
      (ι : (Spec (.of R)).residueField p →+* K),
      algebraMap R K =
        ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p).hom) →
      IsDomain (B ⊗[R] K)) :
    Module.Projective R B
```

The proof was `by sorry`; there was no scoped instance command.

## New

```lean
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] ULift.smulLeft ULift.mulAction ULift.smulZeroClass ULift.distribSMul
  ULift.distribMulAction ULift.smulWithZero ULift.mulActionWithZero ULift.module in
theorem projective_of_geometricallyIntegral_fibres
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (hflat : RingHom.Flat (algebraMap R B))
    (hfibres : ∀ (p : Spec (.of R)) (K : Type (max u v w)) [Field K] [Algebra R K]
      (ι : (Spec (.of R)).residueField p →+* K),
      algebraMap R K =
        ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p).hom) →
      IsDomain (B ⊗[R] K)) :
    Module.Projective R B
```

The signature above is unchanged. Its proof is now complete from the existing
Noetherian approximation and Noetherian projectivity theorems. The docstring now
records that argument. No target definition or statement changes.

## Users

`tools/downstream.py Sheaf.RingTheory.AffineGeometricallyIntegralProjective --uses
Algebra.projective_of_geometricallyIntegral_fibres` lists 64 downstream modules and
finds no downstream textual uses of the theorem name. The rows below include all
64 modules and the item, with current module-claim holders. Each keeps the same
statement and definitions, because only the proof and declaration-scoped elaboration
settings changed. No consumer source needs adapting.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.AffineGeometricallyIntegralProjective | Z6 | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericFreeBlowup | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.AffineGenericLocalizationIntersection | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.RingTheory.FlatAlgebraEtaleProjectiveNeighborhood | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.RingTheory.FreeSubtractionFlatness | B4 | Same theorem type and public instances; no adaptation needed. |
| Sheaf.RingTheory.VerticalPrincipalIdealFibreDetection | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.RingTheory.WeaklyAssociatedTensorFlatFinitePresentation | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.AffineGenericRankBlowup | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.CompleteDevissageProjectiveLocalization | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | E4 | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | P8 | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.LocalGenericBasisUniversalInjective | Q5 | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Same theorem type and public instances; no adaptation needed. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Same theorem type and public instances; no adaptation needed. |

## Status

landed 20261023T132551-L-2301129 2026-10-23 (merge of deliver/Z6/Sheaf.RingTheory.AffineGeometricallyIntegralProjective)
