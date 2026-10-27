## What changed

Filled `AlgebraicGeometry.exists_affine_etale_split_neighbourhood` without changing its
signature. The proof uses the existing unramified etale-local decomposition, converts its
closed-immersion pieces to open immersions, and chooses one affine open simultaneously
inside all piece images and isolating the marked fibre point. Constructed the restricted
copies and remainder by open-immersion lifts and pullbacks. Coproduct extensionality proves
the structure-map equality. A direct injectivity/surjectivity proof gives the required
geometric-lift enumeration with exactly the displayed values.

Added four proved private helper theorems in the item module; no new modules or nodes.
Updated the item's DAG proof and dependency list to match this implementation. Adopted
the required module header and public section; only the statement imports are public.
The import/header record is `coord/changes/U4-affine-etale-split-module.md`.

Validation: the complete delivered Lean file compiled cleanly through `lcompile.py` in
8.5 seconds, exit code 0, with no warnings. Its main theorem signature is byte-identical
to the assigned source; all lines are at most 100 characters. There are no current direct
Lean importers requiring a consumer compile.

Searches: LeanFinder found no scheme splitting theorem; Loogle's `"Etale", "split"`
found finite-algebra splitting, which needs a finite morphism; grep found Mathlib's
`finite_preimage_singleton` and `isDiscrete_preimage_singleton`. The source library's
finite-etale splitting theorem also assumes finiteness of the whole morphism, so it does
not replace this item. Used the stated unramified decomposition instead.

Edge cases: the proof permits an empty original fibre, no split pieces (`n = 0`),
a nonclosed marked point, and independent arbitrary scheme universe `u`. Discreteness,
not closedness of the marked point in the base, supplies the isolating open. Reindexing
uses the number of split pieces, which can exceed the number of original fibre points.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.exists_affine_etale_split_neighbourhood`
(node `lem-trf-affine-etale-split-neighbourhood`).

Holes added: zero. Split-off statements: zero. Holes left in delivered files: zero.
This is a proof from existing declarations, not a new decomposition into sorried lemmas.
The existing unramified-decomposition dependency retains its own proof dependencies.

## No longer needed

Removed import `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`.
The proof uses the already proved
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` API for etale
quasi-finiteness and Mathlib's finite/discrete fibre lemmas.

Removed these proof dependencies from this node:
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-affine-scheme-qcqs`,
`lem-weil-pbc-etale-fibre-discrete-separable-points`,
`def-pc-scheme-fibre`, and
`def-weil-pbc-pointed-etale-neighbourhoods`.
The last definition remains a statement dependency: the neighbourhood's data are
constructed explicitly, so the proof needs no separate category-of-neighbourhoods API.
Other nodes/modules may still use all these declarations; none is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG's second finiteness argument
and removal of closures can be shortened: a discrete fibre already supplies an ambient
open meeting that fibre in exactly the chosen point. One affine shrinking suffices after
intersecting this open with the component images. The prescribed-point geometric lifting
lemma applies directly and needs no auxiliary jointly surjective two-member cover.

The assigned source file lacked the required module header; this delivery supplies it.
The unit's own statements and realized steps are untouched.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
