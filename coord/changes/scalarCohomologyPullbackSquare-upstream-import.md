# AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_square

## Reason

Restore the module quarantined by upstream sync 5f7b33eac. The retired local
scalar-operations module is now empty, so its public import no longer exposes
`Field`, scalar cohomology, or the normalized pullback comparisons. The
composition theorem imports the canonical upstream operations privately from
this module's perspective. Import those operations publicly here because the
square theorem's statement uses them. This repairs the recorded unknown
`Field` error without changing any statement or proof.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition
```

No definition, declaration signature, proof body, attribute or source-library
file changes. The canonical operations module is the one already recorded by
`def-sc-field-linear-module-cohomology-operations`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare | E3 | Restore archived proof; clean single-file compile. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | quarantined; unclaimed | Direct consumer applies the same square theorem twice with unchanged arguments. No adaptation required by this repair. Its own retired operations import remains its separate rework. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | quarantined; unclaimed | Transitive consumer through functoriality; unchanged interface. Separate rework item. |

`tools/downstream.py` reports an unknown module because the assigned source is
quarantined. An import scan over both library roots and quarantine finds exactly
the two consumers above. No consumer or archive is deleted. Both applications
in the direct consumer still match the theorem's unchanged signature. The
DAG attachment and proof dependencies are preserved; its Lean note records
restoration. No target meaning or unit route changes.

## Status

landed 20261020T152959-L-2858319 2026-10-20 (merge of deliver/E3/Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare)
