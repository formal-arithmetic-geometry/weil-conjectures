## What changed

Proved `AlgebraicGeometry.Scheme.Modules.fittingSheaf_arbitrary_pullback` in
`Sheaf.AlgebraicGeometry.FittingSheafArbitraryPullback`, preserving its statement and
all three public definitions. Four proved private helpers handle invariance of the
kernel-minor ideal under a codomain equivalence, tensor generators, the normalized
B-linear affine section equivalence, and the affine sheaf isomorphism.

The proof uses the existing preservation, affine section and presentation Fitting
statements. The global equality follows from the already proved affine comap formula
and `IdealSheafData.ext_of_iSup_eq_top`, avoiding the image-module construction of
step 5 of the original plan. Updated the item's DAG proof and proof dependencies.
All added imports are private proof imports; existing public imports are preserved.

Searches through msearch (LeanFinder, Loogle and grep) found no whole-theorem match.
Loogle found `Submodule.baseChange_span`, which proves the generator clause directly.
Local source search found `IdealSheafData.ideal_comap_appLE`, attached to the closed
node `lem-pc-ideal-sheaf-comap-affine-extension`; this supplies the shorter global route.
The source read was Stacks Divisors, section 31.9, Tag 0C3C and Tag 0C3D, including
its reduction to More on Algebra 07ZA(3). This is below the unit route and preserves it.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.fittingSheaf_arbitrary_pullback`
(blueprint: `lem-trf-fitting-sheaf-arbitrary-pullback`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-off statements. The proof still depends on the previously stated
`LinearMap.presentationFittingIdeal_independence_baseChange` and
`AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_affine_sections`, whose proofs
are other items; it does not claim to close those dependencies.

The argument includes arbitrary morphisms, the empty generating family, and the
unit-ideal convention when r is at least the number of generators. No flatness,
finite presentation, or injectivity of the tensor-pulled ideal inclusion is used.

## No longer needed

Removed the private imports
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf` and
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.
The implementation of this theorem no longer needs these planned dependencies:

- `lem-weil-pbc-module-pullback-structure-sheaf` (module
  `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`): the affine
  comap formula already identifies the extended ideal.
- `lem-weil-pbc-quasi-coherent-module-cokernel-image` (module
  `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`): no
  separate image sheaf is constructed.
- `lem-weil-pbc-spec-tilde-free-module`: the global argument does not need a
  separate quasi-coherence proof for the structure sheaf. There was no direct
  import of a module for this node to remove.

Removed exactly those three obsolete entries from the item's `tool_uses` list.
This is dependency pruning for this proof; no source-library declaration or module
is removed. Other consumers may still need those modules.

## Where the brief, the DAG or earlier work was wrong

The original step 5 is valid but unnecessarily reconstructs the affine description
of the extended ideal, which already has a closed source-library implementation.
Use the closed implementation and affine-cover extensionality directly.
The original statements and definitions require no repair. No new node or change
record is needed because all public interfaces are unchanged.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
