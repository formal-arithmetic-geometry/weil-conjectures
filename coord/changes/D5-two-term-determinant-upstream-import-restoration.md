# AlgebraicGeometry.twoTermDeterminantDerivedCompositionLift

## Reason

Restore the quarantined `Sheaf.TraceFormula.TwoTermPerfectDeterminant` from the
archive named in `coord/rework.tsv`. Its old derived-pullback wrapper is an empty
withdrawn module. The public definitions consequently cannot resolve `derivedPullback`.
The recorded-composition wrapper is also empty; after fixing the first import the
compiler additionally reports unknown `recordedPullbackData_E`,
`recordedDerivedPullbackCounit`, and `recordedDerivedPullbackCounit_universal`.
Import the adopted source modules that now declare these same names. Also migrate
the two proof-dependency wrapper imports to their adopted source modules, preserving
the full planned dependencies rather than silently importing empty wrappers.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedPullbackRecordedComposition
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

The returned packet also removes `set_option warn.sorry false`: the landing scanner
reported the option-name token at line 56 as an unattributed hole. Removing warning
suppression leaves the genuine theorem hole visible and avoids that diagnostic.
The repaired file additionally uses the same two transparency options as its adopted
derived-pullback dependencies. The current default elaboration exceeds 60 seconds;
temporary reduced-heartbeat profiling identifies expensive typeclass/definitional-equality
search in the finite-locally-free fields and recorded composition lift. The complete
module compiles in 19.0 seconds with these options, without changing a declaration.

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

These options affect only elaboration in this file and are not exported to consumers.
No profiling or heartbeat-limit option is retained.
All other bytes of the archived Lean file are unchanged. No declaration signature,
attribute, definition body, theorem body, or docstring changes. In particular the
composition lift still uses the original recorded counits and the section-normalized
tensor comparison; it is not replaced by an arbitrarily chosen composition isomorphism.
The determinant data, rank-zero case, zero object and coherence equations are retained.
The one existing existence/equivalence theorem remains postponed; no hole is added.
No target meaning changes and no target review is reopened by this import migration.
The DAG node and its Lean attachment and full proof plan are preserved verbatim.
The quarantine archive is not removed or modified.

## Users

`tools/downstream.py Sheaf.TraceFormula.TwoTermPerfectDeterminant --allow-missing
--uses exists_twoTermPerfectDeterminantData` reports zero live consumers, because
the item and its 34 transitive consumers are quarantined. A second source inventory
including `quarantine/` finds the following 34 consumers. Only
`Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` imports this item directly;
it uses the import as a proof dependency, with no textual reference to this module's
public declarations. None of the transitive consumers mentions the determinant
model, predicate, data, composition lift or existence theorem. Their statements and
definitions therefore need no adaptation. Holders below were read from current claims.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.TraceFormula.TwoTermPerfectDeterminant` | D5 | Archived source restored; four imports migrated. |
| `Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationStabilityLocus` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.Paper.NearbyCycleSheafFiniteness` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.Paper.PlurinodalProperHypercover` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.Paper.PsiGoodOrientedCohomologyStrata` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.Paper.TraitNearbyBaseChange` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.BoundedConstructibleTransport` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.ExceptionalComponentSpecialization` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.StableCurveDiagramNoetherianModel` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.StableModificationConstructibility` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.StableModificationSpreading` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.TemkinStableModification` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.ValuationMarkingSemistableSeparation` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |
| `Sheaf.TraceFormula.ValuationSemistableDominatesStable` | unclaimed | Quarantined consumer; interface preserved; no adaptation. |

The final restored module compiled alone in 8.8 seconds. The unchanged archived
`FlatLCICanonicalAdjunction` was then checked against the restored module with
`lcompile.py` in dependency order: the item compiled in 9.9 seconds and the consumer
in 7.7 seconds. Both checks succeeded without diagnostics. The temporary consumer
copy was removed from the delivery; no consumer source is changed by this packet.
After repairing the return, the complete item and the unchanged archived direct consumer
were compiled together again, successfully and without diagnostics, in 50.8 and 53.5
seconds respectively. The temporary consumer copy was removed before delivery.

## Status

landed 20261020T211653-L-3486758 2026-10-20 (merge of deliver/D5/Sheaf.TraceFormula.TwoTermPerfectDeterminant)
