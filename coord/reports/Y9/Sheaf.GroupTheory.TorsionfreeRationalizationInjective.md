## What changed

Proved `AddCommGroup.rationalizationMap_injective` in
`Sheaf.GroupTheory.TorsionfreeRationalizationInjective` without changing either public signature
or the definition of `rationalizationMap`. Mathlib already identifies the map `g ↦ 1 ⊗ g`
as localization at the positive integers. Equality of images gives a positive integer
annihilating `x - y`; the given hypothesis then gives `x = y`.

Updated the existing node's proof and proof origin to record this shorter implementation.
The existing three proof dependencies remain: tensor products, module localization, and
localization commuting with tensor product. No definitions or other modules changed.

## Proved and sorry left

Closed the one original hole: `AddCommGroup.rationalizationMap_injective`
(node `lem-trf-torsionfree-rationalization-injective`).
Holes closed: 1. Holes added: 0. Sorries left: none. No split-off statements.
`lcompile.py` compiled the delivered module cleanly (exit code 0, 1.0 seconds).

## No longer needed

Removed the redundant private import `Mathlib.Algebra.Module.LocalizedModule.Basic`;
`Mathlib.RingTheory.Localization.BaseChange` already imports its API.
No DAG node or library module is withdrawn or pruned. The explicit fraction-field
isomorphism, localized tensor-unit isomorphism, tensor symmetry, and negative-integer
case in the previous plan are unnecessary: the direct Mathlib instance uses positive
denominators and exactly the tensor order of the existing statement.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is valid but longer than necessary. In particular,
Mathlib has both `IsLocalization (Submonoid.pos ℤ) ℚ` and
`IsLocalization.tensorProduct_isLocalizedModule`, so reconstructing the localization
to tensor comparison is unnecessary. The unit route and theorem statement stay unchanged.
The zero group and arbitrary universe are covered; the denominator obtained from the
positive submonoid is automatically nonzero. No disputed statements or new nodes.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
