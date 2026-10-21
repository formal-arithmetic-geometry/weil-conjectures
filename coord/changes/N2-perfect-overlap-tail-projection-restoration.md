# AlgebraicGeometry.perfectOverlapTailProjectionComponent

## Reason

Restore the module recorded in `coord/rework.tsv` from its quarantine archive.
The archived module fails against the current library before its theorem is
elaborated: Lean rejects a local irreducibility attribute on `derivedPullback`,
which is already globally irreducible. Remove only that redundant attribute
entry. The complete archived proof then compiles against the current canonical
stage-equivalence, nested-square and projection-prism interfaces.

## Old

The failing local command in the quarantined module, verbatim:

```lean
attribute [local irreducible] derivedPullback perfectHomComposition
  perfectOverlapDerivedPullbackTransport perfectOverlapStageObjectIso
  compositionTo perfectHomComparison Scheme.Hom.resLE
  Scheme.homOfLE morphismRestrict
  Functor.mapDerivedCategory IsPullback.isoPullback Scheme.Opens.toScheme
```

## New

```lean
attribute [local irreducible] perfectHomComposition
  perfectOverlapDerivedPullbackTransport perfectOverlapStageObjectIso
  compositionTo perfectHomComparison Scheme.Hom.resLE
  Scheme.homOfLE morphismRestrict
  Functor.mapDerivedCategory IsPullback.isoPullback Scheme.Opens.toScheme
```

All other archived Lean text is preserved verbatim, including the theorem's
signature, complete proof and public and private imports. There is no change to
a definition, target meaning, statement, or consumer-visible interface.

## Users

`tools/downstream.py --allow-missing --uses perfectOverlapTailProjectionComponent`
reports zero active consumers, since the module and its parent are quarantined.
Searching both library roots and the quarantine archive finds the following
direct consumer, whose invocation at lines 144-145 was checked against the
restored signature. It still supplies the same arguments through `hmap` and the
Boolean branch. No consumer adaptation is required by this restoration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | N2 | Restored with the redundant local attribute entry removed. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | quarantined; not adapted | Its call has the identical signature and conclusion. |

The existing node attachment and every statement and proof dependency are
preserved. The parent node still requires the restored theorem; neither node nor
module is withdrawn. The unit realization route is unchanged.

## Status

landed 20261021T225159-L-3789340 2026-10-21 (merge of deliver/N2/Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent)
