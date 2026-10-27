# ellAdic_isLeftAdjoint_boundedConstructibleLowerStar

## Reason

Restore the zero-hole module quarantined by upstream synchronization at its original
path. Its imported dependencies are now available in the current shared library; no
additional module needs adaptation. The earlier multi-module restoration is superseded.

## Old

The original path lean/Sheaf/AlgebraicGeometry/EllAdicBoundedConstructibleProperAdjoint.lean
is absent. Its complete source is preserved under the matching quarantine/ path.
The archived statement is:

```lean
theorem ellAdic_isLeftAdjoint_boundedConstructibleLowerStar [IsProper g.left]
    [IsFinitenessCoefficient ℓ Λ]
    (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) :
    (boundedConstructibleLowerStar Λ ℓ g).IsLeftAdjoint
```

## New

Restore the archived file byte-for-byte at the original Lean path, with exactly the
same statement and complete certificate-elimination proof above. No signature,
visibility, public import, definition, source-library declaration or target changes.
The existing node and its three proper-adjoint dependencies remain unchanged.

## Users

The module is absent from live lean/. tools/downstream.py consequently reports unknown
module. Source and DAG scans checked the preserved attachment and dependencies. No
consumer requires adaptation because the restored interface is identical to its archive.
The existing unit route through the three coefficient cases is preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | C4 | Restore exact archived module with zero holes. |

## Status

landed 20261022T143008-L-917147 2026-10-22 (merge of deliver/C4/Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint)
