## What changed

Proved `AlgebraicGeometry.projective_nodal_family_geometry` with its existing signature.
The canonical first-Fitting singular subscheme supplies the witness. Three proved private
helpers establish purity of a connected Noetherian space of dimension one, invariance of
ordinary double points under scheme isomorphisms, and preservation of nodal geometric
fibres under base change. Finite fibres follow directly from compactness and discreteness.
The fitting theorem's Over-isomorphism supplies the base-changed inclusion and support;
Mathlib's pullback-map range formula supplies equality of smooth loci.

Added private proof imports of `WeilConjectures.RingTheory.AdicCompletionRingEquiv` and
`Mathlib.Topology.Connected.Clopen`. Updated the item's DAG proof and dependencies.
All existing public imports, definitions and declaration signatures are preserved.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.projective_nodal_family_geometry`
(`lem-trf-projective-nodal-family-geometry`). Zero holes remain in the item, and zero
holes are added anywhere. No split-off statements. The proof uses the existing named
`nodal_family_fitting_singular` theorem, whose separate proof remains a downstream item,
and the uniquely characterized first-Fitting ideal sheaf construction.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite`:
  `lem-pc-zero-dimensional-closed-subscheme-finite` is unnecessary because a discrete
  compact fibre is finite without proving it affine or finite as a morphism.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: Mathlib's fibre homeomorphism
  and pullback-pasting isomorphism suffice.
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`: the projectivity API already
  comes from the unchanged public import of `Morphisms.Projective`.

Removed the proof dependency `lem-weil-pbc-closed-immersion-base-change`: closed immersion
of the base-changed singular inclusion follows instead from its isomorphism to the new
first-Fitting inclusion. No modules are withdrawn; these pruning claims concern this proof.

## Where the brief, the DAG or earlier work was wrong

The former plan omitted the conversion from connected global dimension one to pure
dimension one required by `nodal_family_fitting_singular`. This is now proved directly,
using the Noetherian hypothesis on each geometric fibre. It needs no nodal local algebra.
The former finite-fibre route was longer than necessary. Neither issue requires a
statement or definition repair. The existing unit route is preserved. The completion
transport uses the already proved `AdicCompletion.exists_ringEquiv`, recorded by its
existing DAG node. No new nodes or public statements were introduced.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
