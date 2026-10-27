## What changed

Reduced `WeilConjectures.podReindexing_resolution_preservation` to the existing
round-trip theorem and a new, strictly smaller tensor preservation theorem.
The resolution theorem is moved after `podReindexing_roundTrip_shift` so it can
use its specified module equivalence, without changing any declaration signature.
Its forward functor is an equivalence, so Mathlib gives preservation of all limits
and colimits. Existing exactness gives quasi-isomorphism preservation.
For K-injectivity the proof applies the existing proved
`CochainComplex.isKInjective_map_of_adjunction` to the reverse equivalence.
That theorem transposes a map from an acyclic complex, takes its null homotopy,
and transports the homotopy through the forward functor and adjunction unit.

Added `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseFlatKFlat`, which isolates
only the tensor-based flat and K-flat preservation argument for arbitrary
commutative ring sheaves and an invertible coefficient identification. The item
specializes it to the already constructed finite/completed coefficient family.
The theorem takes an explicitly typed additive functor and an equality identifying
it with the sectionwise construction. This presentation avoids a universe-inference
failure and expensive unfolding of the existing module functor; the item supplies
its existing functor, existing additivity instance, and reflexivity for the equality.
Local instance priorities select the already proved coefficient-universe
sheafification and local-bijectivity results; no imported instance is changed.
The new statement does not assert the specified reverse coefficient family,
K-injectivity, limit preservation, quasi-isomorphism preservation, or any Hom
comparison. It is therefore strictly part of the resolution argument.

Added proof imports for that module and the existing source-library
K-injective preservation theorem in `DualizableTransfer`. Profiling found a slow
definitional comparison in the existing coefficient proof. The proved private
helper `podReindexingConstantNaturality` performs that comparison on abstract
coefficient rings, before specializing to the concrete quotient rings. This
avoids unfolding those rings; every existing signature and definition body stays
unchanged.
Updated the item's DAG proof and added the matching new node. No definition,
public import, target statement, or existing theorem signature changes.
The final remote compile is clean: 58.4 seconds for the item and 1.4 seconds
for the new module, with no profiling options retained.

## Proved and sorry left

Closed one existing hole by decomposition:
`WeilConjectures.podReindexing_resolution_preservation`
(node `lem-pod-reindexing-hom-resolution-model`).
Its combining proof is complete; the K-injective and quasi-isomorphism clauses
and the limit/colimit consequences are proved directly from existing declarations.

Two existing holes remain unchanged in the item, on the same node:

- `WeilConjectures.podReindexing_hom_resolution_model`.
- `WeilConjectures.podReindexing_roundTrip_shift`.

Added one hole:
`AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_flat_kFlat`
(node `lem-pod-sectionwise-flat-kflat`). Its proof is exactly `:= by sorry`;
its docstring and node give the complete tensor/exactness argument.

Actual counts: three holes in the starting item; two in the final item plus one
in the new module. One hole closed, one added, net zero. This is a decomposition,
not a completed proof of the whole resolution-preservation argument. The existing
coefficient uniqueness theorem and its definition are unchanged.

## No longer needed

Removed the redundant private imports `Mathlib.CategoryTheory.Limits.HasLimits`
and `Mathlib.Algebra.Homology.BifunctorShift`: their APIs are already available
through imports needed by the statements. No DAG dependency, library module,
unit statement, or unit step is withdrawn. The unfinished Hom and round-trip
statements still require the original plan's dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The original DAG gives the needed
mathematical tensor argument but has no separate declaration for preservation of
flatness and the independent-coefficient K-flat predicate under arbitrary
invertible ring-sheaf transport. The new node isolates those Steps 4--5. The
round-trip statement already supplies the specified equivalence, so it is reused
instead of introducing a second existence theorem for the same equivalence.

Edge cases for the new statement: arbitrary, including zero, ring sheaves are
allowed; no coefficient prime or invertibility hypothesis is needed; the schemes
may be empty; complexes may be unbounded; K-flat complexes need not have flat
terms. The proof uses exact equivalences and direct sums, never exactness of
infinite products. No module was quarantined, withdrawn, or adapted.

## New nodes

`lem-pod-sectionwise-flat-kflat`, in
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseFlatKFlat`, is the tensor
preservation subargument of Steps 4--5. The source is the current blueprint
`prop-pod-dual-tate-data-compatibility`, Step 1, expanded using Stacks
`sites-modules.tex`, `lemma-tensor-product-pullback` (03EL), and
`sites-cohomology.tex`, `definition-K-flat` (06YN).
LeanSearch, LeanFinder/Loogle and Mathlib grep found no matching statement for
the sectionwise module functor and independent coefficient universe. The new
node uses the same generic site and tensor tools already approved for its parent;
it changes no unit route. No change record is required because no existing
statement or definition changes.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
