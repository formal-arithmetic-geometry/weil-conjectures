# AlgebraicGeometry.ProjectiveBundlePicardClassification.exists_projective_bundle_fiber_twist_model

## Reason

Prove the fibre-and-line model from existing normalized symmetric-algebra pullback,
relative-Proj base change, fixed quotient-line comparison and ordered free comparison.
Remove the unused locally constant line twist import. The theorem signature and
all data definitions stay unchanged. Only the two proved helpers are private.

## Old

The theorem proof was `by sorry`. The module also exported the unused import:

```lean
public import Sheaf.AlgebraicGeometry.LocallyConstantLineTwist
```

## New

The theorem has a complete proof from existing library declarations. Its statement
is verbatim unchanged. The unused import above is removed; the six added imports
are private proof imports. File-local irreducibility protects the existing pullback
and relative-Proj APIs during elaboration and exports no attribute changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveBundleFiberTwistModel | M5 | One hole closed, no new holes. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleFiberDegree | unmodified consumer | Only direct importer; already public-imports LocallyConstantLineTwist itself. Its theorem call is unchanged. |

`tools/downstream.py --uses exists_projective_bundle_fiber_twist_model` finds only
the item and ProjectiveBundleFiberDegree. All other downstream modules pass through
this direct importer, which still exports the removed import independently. No
consumer needs adaptation. The direct importer is compiled against the changed
item and its temporary byte-identical sandbox copy is removed before delivery.
No target statement or target meaning changes.

## Status

landed 20261027T151719-L-1196743 2026-10-27 (merge of deliver/M5/Sheaf.AlgebraicGeometry.ProjectiveBundleFiberTwistModel)
