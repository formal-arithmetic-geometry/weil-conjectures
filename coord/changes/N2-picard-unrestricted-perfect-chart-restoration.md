# AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart

## Reason

Restore the quarantined module assigned by coord/rework.tsv. The archived source fails
against the current library: `derivedPullback` and `derivedPullback_spec` are unknown,
with cascading failures in the comparison and zero-object arguments. Its public import
of Sheaf.AlgebraicGeometry.DerivedPullback now points to a withdrawn empty module.
The adopted source module provides the current declarations recorded by
node def-pc-derived-pullback. Replace the obsolete import with that module.

The restored theorem and all six private helper proofs are preserved verbatim.
No definition, instance, attribute, theorem signature, or mathematical meaning changes.
The existing node attachment and its proof dependencies remain correct. No target
statement or target definition changes, so no new target semantic review is needed.

## Old

The module is absent from lean/ and is preserved at
quarantine/Sheaf/AlgebraicGeometry/PicardSingleRankUnrestrictedPerfectChart.lean.
The archived public import is:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

Restore the archived module to its original Lean path, replacing that one import with:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

All other source text, including the public theorem signature, is identical to the archive.
The public import is necessary because the theorem statement mentions derivedPullback.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart
--allow-missing --uses exists_picardSingleRankUnrestrictedPerfectChart` reports zero current
Lean downstream modules because the item is quarantined. An additional search of lean/
and quarantine/ finds this archived direct consumer, which must remain supported:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | N2 (assigned item) | Restore source and import the adopted derived-pullback API; same theorem and proof. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | quarantined; not adapted | Uses the same chart theorem with the same arguments and conclusion; no source adaptation required. |

The DAG parent lem-sc-picard-universal-single-rank-locus-lfp still requires the chart;
this restoration preserves that dependency and the unit route. No modules are withdrawn.

## Status

landed 20261021T233746-L-857537 2026-10-21 (merge of deliver/N2/Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart)
