# Retire duplicate perfect stalk quasi-isomorphism detection

Retire `Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection` in favour of the
already proved adopted source module
`WeilConjectures.AlgebraicGeometry.PerfectStalkQuasiIsoDetection`. The Sheaf file
is listed in `deleted.txt`; no source-library file or target statement is changed.
The DAG node `lem-sc-perfect-stalk-quasi-iso-detection` is reattached to the
upstream declaration and records its exact source signature and proof dependencies.

The upstream theorem is stronger than the old duplicate: it omits the unused
`IsAffineOpen U` hypothesis `hU`. Specializing the stronger theorem recovers the
old node assertion. The current source tree has zero direct importers of the
Sheaf duplicate, and the adopted parent
`WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedIsoSpread` already imports
and applies the source theorem. No consumer adaptation is needed.

No declarations in `WeilConjectures/` are edited or removed. The unit route and
all mathematical dependency nodes remain in the DAG.

## Reason

This duplicate is an explicitly listed zero-hole retirement. The adopted source
library now contains the complete proved theorem, while the Sheaf duplicate has
no live importers. Retaining both copies duplicates the public declaration and
its private K-projective proof infrastructure.

## Old

The old module publicly imported `WeilConjectures.AlgebraicGeometry.PerfectComplex`
and `WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor`, privately imported
the free-projective, chain-map-lift, comparison, and inverse-homotopy modules,
and declared `perfect_stalk_isKProjective` plus the theorem
`exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso`. Its theorem also
bound an unused `hU : IsAffineOpen U`.

## New

The Sheaf module is withdrawn through `deleted.txt`. The DAG node points to the
unchanged adopted source module and declaration, whose theorem has the same
conclusion and hypotheses except that the unused `hU` binder is omitted. The
source proof and all needed imports remain available in the adopted library.

## Users

`tools/downstream.py --direct` reports zero current importers of the Sheaf
module, and no source declaration mentions the duplicate theorem. The adopted
parent `WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedIsoSpread` already
uses the upstream theorem. Therefore no consumer source adaptation is required;
there are no affected live users.

## Status

landed 20261021T002121-L-1488051 2026-10-21 (merge of deliver/B8/Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection)
source and all target statements are unchanged. The node and change record are
included in this delivery for review.
