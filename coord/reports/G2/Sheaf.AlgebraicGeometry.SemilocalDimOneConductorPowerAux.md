## What changed

Withdraw `Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux`, an unused duplicate
of the proved upstream module. Reattach node
`semilocal-dim-one-conductor-power-aux` to
`WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPowerAux` and record its exact
signature. The upstream theorem omits the unused dimension-one hypothesis and proves
the old statement by direct specialization. Correct the node's wording: surjectivity
is on prime spectra, not on the ring inclusion.

Change record: `coord/changes/retire-semilocal-dim-one-conductor-power-aux.md`.
No upstream file, target, or consumer changes. The unit's route and both proof
dependencies are retained.

Validation: `lcompile.py` compiles an exact upstream-module copy and a scratch theorem
with the full old statement proved by direct application of the upstream theorem.
`#print axioms` for both declarations reports only `propext`, `Classical.choice`,
`Quot.sound`. No direct importers of the withdrawn module remain.

## Proved and sorry left

Zero holes before; zero holes after. Holes closed: none. Holes added: none.
`exists_finite_adjoin_with_jacobson_power` was already proved; its Sheaf duplicate is
withdrawn, while the existing upstream proof remains intact. No split-off statements,
new declarations, or new nodes. This delivery is retirement, not a new proof or a
net reduction in holes.

## No longer needed

Module `Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux` and its duplicate
`exists_finite_adjoin_with_jacobson_power` declaration. The module has zero direct
importers; the historical Sheaf consumer is already absent. Its removed imports are:

- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.RingTheory.Localization.FractionRing`
- `Mathlib.RingTheory.Spectrum.Maximal.Defs`
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
- `Mathlib.RingTheory.Jacobson.Ideal`
- `Mathlib.RingTheory.KrullDimension.Basic`
- `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`
- `WeilConjectures.AlgebraicGeometry.IntegralOverringJacobsonPower`
- `WeilConjectures.AlgebraicGeometry.AdjoinFiniteFractionSpec`

These imports disappear from the retired copy only. Nodes
`adjoin-finite-fraction-spec` and `lem-sc-integral-overring-jacobson-power` and their
upstream modules remain necessary for the retained upstream proof and are not pruned.
The item's node remains attached to its upstream realization.

## Where the brief, the DAG or earlier work was wrong

The live item already has zero sorries and no importers. It is a retirement item in
`coord/retire-items.tsv`; its upstream twin was marked DIFFERENT only because the
upstream statement removed the unused `hdim` argument. An exact old-signature
specialization compiled, so no compatibility wrapper is needed. The old DAG proof
incorrectly described the inclusion into the integral closure as surjective; the
surjective map is the induced map on prime spectra. The mathematical statement,
proof dependencies, and unit route need no change.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
