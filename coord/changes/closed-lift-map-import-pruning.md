# Algebra.ClosedLift: prune unused re-exports

## Reason

The module's three compatibility proofs use only the existing closed-lift construction,
`colimit.ι_desc`, and `AlgHom.comp_assoc`. The ind-principal-Zariski definition and the
scheme-etale and finite-presentation imports are unnecessary for its declarations.
Retain the closed-lift public import and remove the other three re-exports.
No existing declaration signature, visibility, or definition body is changed.
The second reading also adds command-scoped `attribute [-instance] isFiltered_index in`
before `ι_toAlgHom`, `map` and `ι_map`. Without it, Lean selects colimits via the open
filteredness instance and these declarations inherit `sorryAx`. Excluding that instance
for each command selects the existing general-colimit instance instead. The instance is
restored after each command; no downstream instance attribute is changed. The resulting
colimit witnesses are proof-irrelevantly equal, and no construction or target meaning
changes. All five declarations now have only the three permitted axioms.
The etale and finite-presentation APIs needed by the construction remain available
through its upstream import. The separate principal-ind-Zariski definition is unused here.

## Old

The three declarations elaborated with `isFiltered_index` enabled. Their signatures and
source definition bodies are preserved. The old imports were:

```lean
public import WeilConjectures.RingTheory.ProEtale.ClosedLift
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.FinitePresentation
```

## New

`ι_toAlgHom`, `map` and `ι_map` are each preceded by:

```lean
attribute [-instance] isFiltered_index in
```

The retained import is:

```lean
public import WeilConjectures.RingTheory.ProEtale.ClosedLift
```

## Users

The table lists all 25 transitive users returned by `tools/downstream.py`.
No consumer file is included in this delivery. Every source is checked individually
against the sandbox's compiled replacement for `ClosedLiftMap`.
The target statements and all definitions they use retain their exact meaning.
All four direct importers were independently recompiled against the final replacement
and pass; the 25 transitive checks below were performed by the first worker before the
scoped instance repair. Of 25 transitive source checks, 24 compile, while
`CompactSupport` has the same existing tensor-sheaf API type error with and without
the overlay. `TargetsCheck` compiles with its pre-existing long-line warning.
No unrelated repair or forced consumer adaptation is part of this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation | D4 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | E1 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties | E1 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction | G1 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift | G1 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | D2 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections | D2 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction | E3 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.RingTheory.ProEtale.ClosedLiftUnits | F2 | No signature or proof adaptation; checked against the pruned overlay. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | No signature or proof adaptation; checked against the pruned overlay. |
| TargetsCheck | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Existing type error reproduced without the overlay; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No signature or proof adaptation; checked against the pruned overlay. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | No signature or proof adaptation; checked against the pruned overlay. |

## Status

landed 20261015T182202-L-785252 2026-10-15 (merge of deliver/E3/Sheaf.RingTheory.ProEtale.ClosedLiftMap)
