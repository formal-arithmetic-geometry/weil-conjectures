# AlgebraicGeometry.perfectOverlapNestedPullbackSquare_on_image

## Reason

The returned restoration packet was byte-identical to the current library: its
redundant local `derivedPullback` attribute had already been removed there. Do not
repeat that restoration. Instead remove this theorem's unnecessary dependency on
the Sheaf composition-helper adapter by using the adopted source's already-proved
private composition helpers through a proof-only `import all`.

## Old

```lean
import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle
```

The proof refers to the adapter's public `compositionTo` and
`compositionTo_triangle`.

## New

```lean
import all WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangle
```

The same proof now refers to the source module's private `compositionTo` and
`compositionTo_triangle`. Their types and constructions are the same as those of
the adapter. The complete proof, `pinnedComposition_eq`, theorem signature,
public imports, and comparison definitions are preserved. No adopted source file
is changed. No definition or target meaning changes.

The node's second proof step and `proof_origin` record direct use of the adopted
source helpers. Its mathematical dependencies and Lean attachment stay intact;
`lem-pc-perfect-hom-comparison-triangle` already names the source module.

## Users

`tools/downstream.py` finds one direct importer and one external term consumer:
`PerfectOverlapNestedSiteCompatibility`, whose `normalized_gamma_rhs` applies the
unchanged theorem with `g iY iX hP hT M`. A proof-only import changes none of the
consumer's visible declarations or expected types. The consumer is checked without
source edits and is not delivered as an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization | V8 | Uses the source composition helpers directly; removes the Sheaf helper import. |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility | unclaimed; not adapted | Same public signature and imports; existing application unchanged. |

The Sheaf helper module has other consumers and is retained in the library. No
module is withdrawn. The parent node and unit route are unchanged.

## Status

landed 20261021T204051-L-3933240 2026-10-21 (merge of deliver/V8/Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization)
