## What changed

Proved `SheafOfModules.exists_quotient_map_small_models` in
`Sheaf.Algebra.Category.ModuleCat.Sheaf.QuotientMapSmallModels`, preserving its exact
statement and all three public imports. No additional imports are needed.

The family consists of categorical cokernels of the actual literal inclusions.
For an epimorphism, the ranges of the sectionwise maps of its categorical kernel
form a restriction-stable submodule. The sectionwise injections give a presheaf
isomorphism from the categorical kernel to that submodule, transferring the sheaf
axiom and the kernel property. Mathlib's `Abelian.epiIsCokernelOfKernel` and
cokernel uniqueness provide the isomorphism with the given target, including the
required equality of quotient maps. The existing node's proof and proof origin
record this realization of the same kernel-parametrization argument.

The module compiled successfully through `lcompile.py` (6.2 seconds on the server).
Edge cases include the zero sheaf, empty space, zero and full subsheaves, and an
isomorphism as the given epimorphism: categorical kernels and cokernels handle
all of them without any nonemptiness or sectionwise-surjectivity hypothesis.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.exists_quotient_map_small_models`
(node `lem-weil-pbc-module-quotient-map-small-models`).
One of one holes proved; zero holes remain and zero holes were added.
No statements were split off.

## No longer needed

None. All original imports are needed by the statement, and both declared proof
dependencies (`def-weil-sheaf-of-modules-category` and `def-sp-abelian`) are used.
No nodes or modules are withdrawn or pruned. No additional modules were imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The DAG's sectionwise kernel construction can
be implemented more directly by transporting the existing categorical kernel
through its sectionwise range isomorphism; the proof record now says so.
The statement, dependency lists, and unit route are unchanged.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
