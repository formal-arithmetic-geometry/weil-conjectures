## What changed

Retired `Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily`, the assigned
retirement item in `coord/retire-items.tsv`. Its node
`lem-sc-exterior-dual-pairing-local` now records the unchanged upstream theorem
`AlgebraicGeometry.exterior_dual_pairing_local` in
`WeilConjectures.AlgebraicGeometry.DeterminantDualAlternatingFamily`.

Adapted the sole direct consumer `Sheaf.AlgebraicGeometry.DeterminantDualPairing`:
replace the private import, choose the upstream alternating family, and compose
with the sectionwise linear map of `dualMap exteriorSheafIsoExteriorPower.hom`.
`LinearMap.compAlternatingMap` preserves the alternating structure. The proved
hom-wedge comparison yields exactly the former determinant evaluation formula.
The consumer's signature and public imports are unchanged. Its construction node
records this transport; the local-family node records the upstream proof.

The consumer compiles cleanly (11.9 s). An import-only counterfactual fails with
the expected `exteriorPower`/`exteriorSheaf` codomain mismatch. A compiled axiom
probe (11.6 s) reports only `propext`, `Classical.choice`, and `Quot.sound` for
both the upstream local-family theorem and the adapted construction theorem.
Change record: `coord/changes/retire-determinant-dual-alternating-family.md`.

## Proved and sorry left

Zero of zero holes closed in the item: it was already proved when assigned.
This is a duplicate retirement, with one module pruned. Zero holes added or left
in any delivered Lean module; no statements split off. The consumer theorem
`AlgebraicGeometry.exterior_dual_pairing_exists`
(`lem-sc-exterior-dual-pairing-construction`) has a complete proof from the
upstream `AlgebraicGeometry.exterior_dual_pairing_local`
(`lem-sc-exterior-dual-pairing-local`) and the proved canonical comparison.

## No longer needed

Withdrawn module and removed consumer import:
`Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily`.
The mathematical node stays, attached to its upstream twin; no node is deleted.
The upstream local-family proof has no comparison dependency, so its node drops
`lem-sc-exterior-sheaf-comparison` from `proof_deps` and proof-step `uses`.
The comparison is still needed by the consumer's explicit transport and its
extensionality argument. The fixed-tuple functional and dual extensionality
nodes remain needed by the upstream proof. No other modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with a hole or assigned repair. This
item is a listed retirement with zero current holes. The upstream theorem's
codomain uses `exteriorPower`, whereas the older consumer uses `exteriorSheaf`;
a private import replacement alone fails to compile. The existing canonical
comparison resolves the mismatch without changing either mathematical statement
or target, adding assumptions, or editing any adopted upstream source.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
