## What changed

Proved `AlgebraicGeometry.Scheme.sfIntrinsicOpenUnit_isIso` in
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit` with its signature unchanged.
The source library already proves full faithfulness of the fixed-scalar open extension.
Its composite with the two canonical coefficient equivalences is fully faithful, so
Mathlib makes the unit of the specified intrinsic adjunction invertible. Added a
proof-only import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful`.
Updated the proof docstring and the item's DAG proof, proof dependencies and origin.
No definition, theorem statement or target changed. No new modules or nodes.
Public-import change record: `coord/changes/F8-intrinsic-open-unit-import-pruning.md`.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.sfIntrinsicOpenUnit_isIso`
(node `lem-exc-proetale-open-unit`). Added 0 holes; split off 0 statements.
There are no `sorry`s left in the delivered Lean module. Existing dependencies,
including the coefficient realization equivalence, retain their prior proof status.
The complete module compiles cleanly through `lcompile.py` (3.1 seconds).
The sole downstream consumer,
`Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison`, also compiles unchanged
against the sandbox version (6.6 seconds), verifying the removed public import
requires no consumer adaptation. Its unchanged test copy is not part of the delivery.

## No longer needed

Removed the unused public import
`Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`; no declaration from
it is used in this theorem's statement or proof.

The old direct presheaf/sheafification route is unnecessary here. Removed from the
item's proof dependencies: `def-weil-presheaf-modules-sheafification`
(`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`),
`lem-cbc-sieve-slice-sheafification`
(`Mathlib.CategoryTheory.Sites.CoverLifting`), and
`lem-weil-proetale-weakly-etale-localization`
(`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`). Their modules were not
directly imported by the original item, and may remain needed by other consumers.
The canonical extension definition and adjunction remain necessary. The replacement
full-faithfulness dependency is already Lean-closed in the pinned source library;
the item's unit has no realized node steps bypassed by this shorter route.

## Where the brief, the DAG or earlier work was wrong

The inherited plan overlooked the existing, proved
`ProEtale.fullyFaithfulOpenImmersionLowerShriek`, so rebuilding the sectionwise
sheafification argument is unnecessary. Its node
`lem-sfb-finite-extension-by-zero-fully-faithful` has a stale `lean.module` path;
the correct current path appears in its `lean_audit.slopmaster2` record and is the
module imported by this delivery. No node attachment was changed.

The proof uses no extra nonemptiness, nonzero-ring, or quasi-compactness hypotheses;
it also applies to the empty scheme/open, identity immersion and zero ring, as does
the existing full-faithfulness theorem.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
