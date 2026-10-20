# AlgebraicGeometry.isIso_localized_stalk_component_of_residue_homology

## Reason

Restore the complete module preserved by the current rework row at
`quarantine/Sheaf/AlgebraicGeometry/RankOneResidueStalkComponent.lean`.
The cluster restore removed it from the live library. The archived module imports
an empty, withdrawn Sheaf derived-pullback module; consequently `derivedPullback`
is unavailable in its public theorem signature. Import the canonical adopted
module directly, as its restored residue-coefficient dependency already does.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The archived declaration signature, docstring, visibility and complete proof body
are preserved verbatim. No mathematical statement or definition changes. No target
requires statement re-review.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent | K2 | Restored with the canonical public import; compiles and uses only the three allowed axioms. |
| Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk | quarantined; separate rework item | Direct proof importer; its existing application has identical arguments and conclusion. No adaptation required. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | quarantined; separate rework item | Direct proof importer; both existing applications have identical arguments and conclusion. No adaptation required. |

`tools/downstream.py ... --uses isIso_localized_stalk_component_of_residue_homology`
reports unknown module because this item is quarantined and absent from `lean/`.
A search of both live Lean roots and `quarantine/Sheaf/` finds exactly the two
external consumers above. Their three applications were read against the restored
signature, which also matches the node's recorded Lean statement verbatim. Neither
consumer is withdrawn or modified. The dependency and unit route are preserved.
There are no live direct importers requiring recompilation for this import repair.

## Status

landed 20261020T230800-L-611952 2026-10-20 (merge of deliver/K2/Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent)
