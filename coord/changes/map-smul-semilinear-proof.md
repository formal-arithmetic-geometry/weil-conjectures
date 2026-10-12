# ModuleCohomologyFMapData.map_smul proof import and semilinear helper

## Reason

The scalar compatibility proof uses the semilinear-lift helper declared in the new
proof-support module `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear`.
The import is plain (`import`), so the helper is available while elaborating this
proof without becoming a transitive public import. The existing target theorem's
signature and meaning are unchanged; the helper is a new named theorem with its own
DAG node because the direct construction is deferred.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

 theorem ModuleCohomologyFMapData.map_smul ... := by sorry
```

No semilinear helper module existed.

## New

```lean
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear

 theorem ModuleCohomologyFMapData.map_smul ... := by
  obtain ⟨f, hf⟩ := D.map_semilinear p
  rw [← hf x, ← hf (r • x)]
  exact f.map_smulₛₗ r x
```

The added module declares
`ModuleCohomologyFMapData.map_semilinear` with the statement recorded in
`lem-weil-pbc-module-cohomology-fmap-semilinear-lift.json`; its proof remains a
named `sorry` pending the resolution-comparison construction.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMapScalarCompatibility | N2 | proof elaboration only; theorem signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties | unclaimed | imports the scalar compatibility theorem; no signature or definition change |

## Status

landed 20261012T173846-L-3301164 2026-10-12 (merge of deliver/N2/Sheaf.AlgebraicGeometry.ModuleCohomologyFMapScalarCompatibility)
