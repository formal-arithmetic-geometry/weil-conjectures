# AlgebraicGeometry.finite_singleton_fibre_stalk_ring

## Reason

Repair the landing refusal at returned head `55d96d8c463`. The source ledger counts
an option-name component in `warn.sorry` as an unattributed hole. Remove the obsolete
warning-suppression command entirely. This changes only diagnostics within this file;
all declaration signatures, definitions, public imports and proof dependencies retain
their meanings. The module compiles with no warnings after removal.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

The theorem proof in the retained delivery closes its original named hole. The
existing proof-only import of `WeilConjectures.Topology.PresheafModuleStalkFunctor`
is removed because the proof uses Mathlib's scheme ring stalk API directly.
Neither edit changes an importing module's available public declarations.

## Users

`tools/downstream.py Sheaf.TraceFormula.FiniteSingletonFibreStalkRing --uses
finite_singleton_fibre_stalk_ring` lists the following 55 downstream modules.
No downstream source currently mentions the declaration name in Lean code; the
direct consumer still has its planned proof hole. The option is file-local and its
removal changes no downstream statement or definition, including any target.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.FinitePushforwardModuleFinitePresentation | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ElementaryDevissageFinitePresentation | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | E4 | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | P8 | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No semantic or interface effect; no adaptation required. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No semantic or interface effect; no adaptation required. |

## Status

landed 20261023T132219-L-2234752 2026-10-23 (merge of deliver/W4/Sheaf.TraceFormula.FiniteSingletonFibreStalkRing)
