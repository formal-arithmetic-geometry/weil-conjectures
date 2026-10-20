# AlgebraicGeometry.singleComplexAffineBaseChange imports

## Reason

Restore the quarantined affine base-change module from the archive named by its
`coord/rework.tsv` row. The recorded global-build failure imported the old Sheaf
stalk-condition implementation together with the adopted upstream derived-pullback
implementation, producing two declarations named `AlgebraicGeometry.derivedPullback`.
Use the upstream stalk-condition module, matching both other existing imports.
The old Sheaf stalk-condition module is now an empty withdrawn module; keeping its
import would retain an obsolete dependency instead of stating the actual provider.
The theorem signature and complete proof are unchanged from the quarantine archive.
No source-library module, definition, statement or target is changed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction
```

## Users

`tools/downstream.py Sheaf.Algebra.Homology.SingleComplexAffineBaseChange --uses
singleComplexAffineBaseChange` reports the module unknown because it is quarantined.
An independent recursive search of `lean/` and `quarantine/` for the module path and
the declaration name found no importers or callers of the public theorem: only its
own archived declaration and the separate upstream Core theorem. The Core theorem
and its open-affine consumer are unchanged. Existing DAG parents and the item's Lean
attachment remain intact; this restoration does not withdraw the item.
The upstream qcqs import already publicly imports the upstream stalk-condition
module, so this edit adds no new public declarations beyond that existing import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChange | A5 | Restored; explicit stalk-condition import uses the adopted implementation; theorem signature and proof unchanged. |

## Status

landed 20261020T174716-L-782937 2026-10-20 (merge of deliver/A5/Sheaf.Algebra.Homology.SingleComplexAffineBaseChange)
