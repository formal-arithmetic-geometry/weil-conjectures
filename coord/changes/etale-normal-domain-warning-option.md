# AlgebraicGeometry.etale_normal_domain_finite_factors

## Reason

The return at head `07934308444` reports an unattributed hole at the module
command `set_option warn.sorry false`. The source-only landing scanner matches
the `sorry` component of this option name. Remove the unnecessary suppression:
the theorem is fully proved, with no literal or transitive proof holes.
The preflight classifies this command removal as an interface change and asks
for this record. No theorem statement or mathematical definition changes.

## Old

The removed module command, verbatim:

```lean
set_option warn.sorry false
```

## New

The command is absent. Lean uses its default warning setting. The theorem's
signature, universes, visibility, and both public imports remain unchanged.
The theorem body is the retained complete proof, rather than the library's hole.

## Users

`tools/downstream.py Sheaf.TraceFormula.EtaleNormalDomainFiniteFactors --uses
AlgebraicGeometry.etale_normal_domain_finite_factors` lists 22 downstream modules
and the item's own occurrence of the declaration. The two direct importers are
`Sheaf.TraceFormula.NormalTensorComponentJoinModel` and
`Sheaf.AlgebraicGeometry.DmFiniteNormalizationCharts`; neither currently mentions
the theorem by name. Every downstream module keeps the same statement and all
of its existing imports. A local warning setting supplies no mathematical data
or typeclass instances to these users, so no adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ArtinHenselianTensorResidueDichotomy | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ArtinJoinTheorem63 | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ArtinTensorEtaleAcyclic | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.DmFiniteNormalizationCharts | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveStrictLocalIntersectionAcyclic | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.NormalTensorComponentJoinModel | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No imported declaration, signature, instance or notation changes; no adaptation required. |
| Sheaf.TraceFormula.EtaleNormalDomainFiniteFactors | E2 | Own module: complete proof and remove unnecessary local warning suppression. |

## Status

landed 20261023T123446-L-1192438 2026-10-23 (merge of deliver/E2/Sheaf.TraceFormula.EtaleNormalDomainFiniteFactors)
