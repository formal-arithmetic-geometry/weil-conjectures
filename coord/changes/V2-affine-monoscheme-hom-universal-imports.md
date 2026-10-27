# Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal

## Reason

Convert the assigned legacy-header file to the required module format. Preserve the
signatures and body of `AlgebraicGeometry.Monoscheme.affinePullback` and the signature
of `AlgebraicGeometry.Monoscheme.affine_hom_universal`. Add two private proof imports
for the existence and rigidity steps. Remove unused direct imports: FineFanBlowup is
already a public import of MonoschemeToricRealization; Sites belongs to the remaining
basis arguments in the split-off lemmas, not the combining proof.

## Old

```lean
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Mathlib.Topology.Sheaves.SheafCondition.Sites
```

## New

```lean
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.AlgebraicGeometry.AffineMonoschemeHomExistence
import Sheaf.AlgebraicGeometry.AffineMonoschemeHomExt
```

The declarations follow an `@[expose] public section`. Both new modules publicly
import MonoschemeToricRealization and declare one theorem apiece. Existing mathematical
interfaces are unchanged. No target statement or shared definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal | V2 | Combines the two new lemmas; compiled against both. |

A source search of `lean/` finds no direct importer of the assigned module and no
external occurrence of its qualified `Monoscheme.affinePullback`. Consequently there
are no existing direct importers to adapt or compile. DAG parents are retained: in
particular MonoidSpectrumHomUniversal remains downstream of this item in the DAG,
and its statement was not used to prove this item. Zero Lean importers is not treated
as permission to withdraw any module or node.

## Status

landed 20261026T092841-L-3472970 2026-10-26 (merge of deliver/V2/Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal)
