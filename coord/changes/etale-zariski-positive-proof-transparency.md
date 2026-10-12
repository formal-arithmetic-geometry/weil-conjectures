# AlgebraicGeometry.Scheme.Modules.etaleZariskiAbelianPositiveComparison

## Reason

The comparison proof only manipulates existing tensor-section sheaves and their
cohomology maps; it does not compute the sectionwise tensor construction.
Unfolding `tensorPullback` and `tensorPullbackObj` during elaboration is expensive.
Declare those two existing constructions locally irreducible for this proof.
This local transparency setting does not propagate to importing modules.
The delivery checker conservatively treats changes to top-level commands as
interface changes, which is why this record accompanies the local attribute.

## Old

No local reducibility command appears between `set_option autoImplicit false`
and the original theorem's docstring. The original theorem body is `by sorry`.
All existing declaration signatures and public imports are those of the base.

## New

```lean
attribute [local irreducible] tensorPullback tensorPullbackObj
```

The command occurs before the unchanged theorem docstring. Its effect is local
elaboration transparency only; the constants' definitions, theorem signature,
visibility, public imports, and mathematical meaning are unchanged. The theorem
now has a complete composition proof from the named independent intermediate
statements. No target statement or definition changed, so no target review reopens.
Three new modules have their own DAG nodes. No existing dependent module is adapted.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison | W3 | Local proof elaboration avoids unfolding the tensor construction. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | unclaimed | Same public theorem signature and imports; local transparency does not escape the file. |

`tools/downstream.py --uses etaleZariskiAbelianPositiveComparison` lists the declaring
module and the single direct user above. It also lists 136 modules downstream in
the import graph, all of which receive the same existing interface. The sole direct
importer imports this module privately. This delivery changes no existing public
signature, removes no public import and adds no global instance or attribute.
No compiler failure forces an adaptation, and no adaptation is delivered.

## Status

landed 20261012T184356-L-4024246 2026-10-12 (merge of deliver/W3/Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison)
