# Profinite.CondensedRing

## Reason

Restore the source module listed in `coord/rework.tsv` after the cluster-restore rollback
(recorded at 2026-10-20T10:47:43Z). Its source is preserved in
`quarantine/Sheaf/Topology/ProfiniteCondensedRing.lean`; the live module is absent.
Restoration supplies the missing general condensed-ring input type again. It does not
select coefficients presented by a topological ring. No mathematical definition repair
beyond reinstating the archived interface is required: the archive compiles as written.

## Old

The live path `lean/Sheaf/Topology/ProfiniteCondensedRing.lean` is absent. The archived
interface, restored verbatim, is:

```lean
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing

abbrev CondensedRing : Type (u + 2) := Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
```

## New

Restore the whole archived module, including its original documentation and public import.
The definition is exactly:

```lean
abbrev CondensedRing : Type (u + 2) := Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
```

## Users

`tools/downstream.py Sheaf.Topology.ProfiniteCondensedRing --uses Profinite.CondensedRing
--allow-missing` reports zero live downstream modules: the users are quarantined too.
An additional search of both live and quarantined sources finds the consumers below.
Their input universes, underlying ring objects, and commutativity hypotheses are preserved.
No consumer is adapted or restored in this packet; each has its own rework assignment.
The existing node attachment, proof dependencies and unit route are preserved. Since this
restoration reinstates the identical definition, no target statement acquires a new meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | no local claim record | Quarantined direct importer and declaration user; identical restored interface; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | no local claim record | Quarantined direct importer and declaration user; identical restored interface; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | no local claim record | Quarantined direct importer and declaration user; identical restored interface; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | no local claim record | Quarantined direct importer and declaration user; identical restored interface; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentSections | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.FiniteWindow | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | no local claim record | Quarantined declaration user; identical restored interface; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | no local claim record | Quarantined declaration user; identical restored interface; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | no local claim record | Quarantined direct importer and declaration user; identical restored interface; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | no local claim record | Quarantined declaration user; identical restored interface; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | no local claim record | Quarantined direct importer; identical restored interface; no adaptation. |

## Status

landed 20261021T020958-L-2686157 2026-10-21 (merge of deliver/B4/Sheaf.Topology.ProfiniteCondensedRing)
