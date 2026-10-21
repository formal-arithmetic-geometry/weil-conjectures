# AlgebraicGeometry.Scheme.localZeroBottomModel_pullback

## Reason

Restore the quarantined module named in `coord/rework.tsv`. Its complete proof is retained,
but its statement imported vocabulary only through the now-empty withdrawn Sheaf module.
The original fails to elaborate its public signature with unknown identifiers `Scheme`
and `HasDerivedCategory`. The adopted source module supplies the required public interface.

## Old

The archived module header contains:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
```

The live item source is absent; its declaration and proof are preserved in
`quarantine/Sheaf/AlgebraicGeometry/LocalZeroBottomModelPullback.lean`.

## New

The restored module header contains:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
```

All remaining source text is identical to the quarantine archive. In particular the public
theorem signature, private helper, proof bodies, universes, hypotheses, and conclusion
are unchanged. No source-library file or target statement is changed. The restored theorem
has zero holes and uses only the three permitted axioms.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback | G1 | Restore source and repair its public vocabulary import. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback | unclaimed, quarantined | Sole direct source importer; existing theorem application has the unchanged type. No edit. |

`tools/downstream.py` reports the item unknown because its live source is quarantined.
A direct search of `lean/Sheaf`, `lean/WeilConjectures`, and `quarantine` finds only the
quarantined importer listed above. No live consumer needs a forced adaptation. The DAG
attachment and all dependencies remain intact; this is not a withdrawal.

## Status

landed 20261021T002933-L-1580551 2026-10-21 (merge of deliver/G1/Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback)
