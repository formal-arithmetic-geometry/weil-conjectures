## What changed

Proved `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel`
in `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`, preserving its full signature.
The source library already proves the constructible model result. Convert the given
cohomology bounds with `DerivedCategory.isGE_iff` and `isLE_iff`, and cohomology
constructibility with `Scheme.isConstructibleEtaleModuleSheaf_iff`. Apply
`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`, convert each model term back,
and reverse its isomorphism. The converse uses `hasTorAmplitudeIn_iff_exists_flatModel`.
The original unit construction remains inside the existing source theorem: lifting,
class resolution, constructible kernels/cokernels, and the lower good truncation.
The node proof and proof origin now record this reuse explicitly.

Validation: both the initial proof and the version with redundant proof imports removed
compiled cleanly through `lcompile.py`. An appended `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The conversion does not exclude the zero ring, empty scheme, zero complex, or singleton
interval: it only transfers existing bounds and constructibility witnesses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel`
(node `lem-sf-etale-flat-constructible`).

Holes added: 0. Holes remaining in the item: 0. No split-offs or new modules.
The axiom check also verifies that the theorem has no transitive sorry dependency.

## No longer needed

Removed these redundant direct proof imports:

- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass`
- `WeilConjectures.CategoryTheory.Abelian.Flat.Basic`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`

They remain transitively imported by the existing source flat-model theorem and used
in its construction. Consequently no underlying DAG node or library module is pruned.
All six original proof dependencies remain needed, with four packaged by the existing
constructible-model theorem. The source flat-model module and finite-value comparison
module are the only direct proof imports needed by this proof.

## Where the brief, the DAG or earlier work was wrong

No false statement, definition repair, or unit-route departure was found. The original
six-step plan is already implemented by the proved source theorem; repeating its class
instances and construction in this module is unnecessary. This delivery supplies only
the finite-value interface conversion and repackaging.

Searches: LeanFinder for bounded constructible etale Tor-amplitude models returned
unrelated etale geometry and derived t-structure results; Loogle did not resolve
`IsZero`; the search service grep had no match. Direct `rg` and source inspection found
`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`, which is used here.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
