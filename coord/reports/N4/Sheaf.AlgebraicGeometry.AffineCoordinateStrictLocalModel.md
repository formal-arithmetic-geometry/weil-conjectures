## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal.exists_model` by a complete
construction of its `Model`, relative to the existing closed-immersion Cartesian
comparison and one strictly smaller new polynomial closed-fibre comparison lemma.

The geometric argument is proved in private helpers in the assigned module:

- `inclusion_over` and `inclusion_coord` compute the explicit zero insertion.
- `inclusion_zeroLocus` proves its universal property on arbitrary test schemes
  directly from `AffineSpace.homOfVector` and `AffineSpace.hom_ext`.
- `inclusion_closed` proves it is a closed immersion: forgetting the selected
  coordinates is a separated retraction, so zero insertion is its closed section.
- `spec_section` records the global-section naturality used in the ring argument.
- `coordinate_quotient` constructs the factor map B/J to C, constructs its inverse
  on spectra by the coordinate-zero universal property and the existing Cartesian
  comparison, proves both inverse equations by monomorphism cancellation, and
  proves exactly the specified canonical ring-map equation.
- `evaluation_kernel` and `coordinate_evaluation` turn maximal-ideal membership
  into vanishing of the original coordinate sections at the geometric point.

Finite affine-space smoothness supplies the smoothness field, including zero
variables. The theorem assembles all these fields with `exists_fibre_models`.
No target statement, original public signature, binder, universe, definition body,
instance or attribute changes. The 12 existing data declarations are moved
unchanged into the new `AffineCoordinateStrictLocalData` module and publicly
re-exported by the item. `Model` stays in the original module. This permits the
new fibre-comparison module to use `FibreModels` without an import cycle. All 14
original signatures were checked with the project's declaration parser.

The new `AffineCoordinateStrictLocalFibreComparison.exists_fibre_models` states
only old proof steps 5--8. It assumes vanishing of geometric coordinate evaluations
and supplies the two polynomial fibre models and their canonical comparison. It
has no conclusion about the closed immersion, its universal test-scheme property,
the geometric point factorization or the strict-local quotient B/J. Those are the
substantial geometric part proved here; the split is not an equivalent renaming
of `exists_model`.

Change record:
`coord/changes/N4-affine-coordinate-strict-local-data-extraction.md`.
No direct Lean importer of the original module exists in the checked source
snapshot. Its DAG parents, including unfinished parents, are preserved. No other
existing Lean module or other module's existing node is changed.

Server compilation passed for all three modules: data 19.3 seconds, fibre comparison
3.1 seconds, and the assigned module 7.4 seconds. The final assigned-module compile
reported no warnings. No direct importer exists to require a compatibility compile.

## Proved and sorry left

Original holes closed: 1,
`AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal.exists_model`
(node `lem-trf-affine-coordinate-strict-local-model`).

New holes added: 1,
`AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal.exists_fibre_models`
(node `lem-trf-affine-coordinate-strict-local-fibre-comparison`), in its own new
module with proof exactly `:= by sorry`, sources and a complete proof in words.
It is the polynomial closed-fibre part of the original argument.

The assigned module has zero remaining sorrys. The new data module has zero
sorrys. The delivery therefore decomposes the original hole, with net hole change
zero; it does not claim a proof free of sorry dependencies. In particular the
existing `isIso_strictHenselizationClosedImmersionCartesian` remains an imported
stated dependency, as intended by this stage.

The geometric proof handles K empty and K all coordinates, r=0, nonreduced test
schemes and arbitrary non-Noetherian bases: its uniqueness is equality of scheme
morphisms, and the quotient construction uses the actual ideal span. The new
fibre statement also permits nonmaximal evaluation primes. For K empty its two
quotients coincide; for K all coordinates the polynomial quotient is kappa;
for r=0 there are no coordinate generators. No omitted hypothesis is required
in these cases.

## No longer needed

Removed the proof import `Mathlib.AlgebraicGeometry.Gluing` and the dependency
`lem-weil-pbc-scheme-morphism-gluing` from the item's proof and `proof_deps`.
The affine-space universal property proves the coordinate-zero construction and
its uniqueness globally; no chart gluing or finite reindexing argument is needed.
Removed its obsolete parent `tool_uses` entry as well.

Removed the direct proof import
`Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison` from the assigned module.
Its node `lem-exc-affine-strict-local-ring-comparison` remains needed in the
polynomial fibre lemma's plan, as does
`lem-trf-smooth-strict-local-closed-fibre-model`. They are isolated in that genuine
remaining part, not pruned from the mathematical argument. The new sorry module
imports only its statement data; its proof dependencies are recorded in its node.

The original public imports for affine space, localization at a prime, strict
henselization presentations, the canonical map and geometric evaluation move to
the data module and remain publicly available through the item. They are not
mathematical pruning. Smoothness and closed-immersion public imports remain in
the item. No existing declaration or module is withdrawn, and no source-library
declaration is removed or changed. No claim is made that a whole library module
has left the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The coordinate-zero geometry does not require the planned chart quotient/gluing
construction. Its global universal property is already supplied by the affine
space API; a separated retraction proves closedness. The Cartesian comparison's
Lean declaration supplies an isomorphism of a pullback, rather than an explicit
kernel formula. The proof above extracts the quotient isomorphism constructively
from that actual signature, including its canonical-map equation.

The remaining polynomial comparison involves the coordinate-specific affine
fibre identifications, two pointed algebraic presentations and their simultaneous
residue-compatible uniqueness. The existing smooth closed-fibre and affine
strict-local comparisons are more general statements; they do not state this
assembled coordinate package verbatim. This work leaves exactly that part as a
new node. No original statement is disputed or weakened; the unit and chapter
route are unchanged.

## New nodes

`def-trf-affine-coordinate-strict-local-data` records the unchanged explicit
coordinate constructions and the `FibreModels` conclusion-data type, moved into
`Sheaf.AlgebraicGeometry.AffineCoordinateStrictLocalData`. This is a data type,
not an assertion of its inhabitation. All data remains explicitly constructed;
no definition chooses an arbitrary witness from a holed existence theorem.

`lem-trf-affine-coordinate-strict-local-fibre-comparison` records
`Sheaf.AlgebraicGeometry.AffineCoordinateStrictLocalFibreComparison.exists_fibre_models`,
the genuinely smaller polynomial closed-fibre comparison of old steps 5--8.
Its node and docstring give the polynomial evaluation, prime quotient, ambient
fibre comparison, quotient comparison and uniqueness argument with their sources
and existing stated dependencies. LeanSearch, Loogle and Mathlib-source searches
found no match, as recorded in the node and the session search log.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
