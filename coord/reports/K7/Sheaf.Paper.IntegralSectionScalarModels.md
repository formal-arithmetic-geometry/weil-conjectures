## What changed

`Sheaf.Paper.IntegralSectionScalarModels` now proves
`AlgebraicGeometry.ProEtale.integralSectionScalarModels` from a scalar-compatible
comparison on the single lifted regular module. Its statement and all original
public imports are unchanged. The proof uses the existing
`ContinuousScalarPresentation.ordinary_presentation`, compares finite free modules
by preserved biproducts, checks the presentation-map square entry by entry, and
uses `PreservesCokernel.iso` and `cokernel.mapIso` to compare the two cokernels.
These are complete private Lean proofs in the item module, not additional holes.

The new module `Sheaf.Paper.IntegralSectionRegularScalars` defines the two actual
composite functors as irreducible wrappers and proves their finite-colimit
preservation from the existing exactness and adjunction results. Its one
remaining theorem concerns only their values and scalar endomorphisms on
`ULift A`. No witness from that theorem is used to define data.

The new proof imports are `import all Sheaf.Paper.ContinuousScalarFinitePresentation`,
`Mathlib.Algebra.Category.ModuleCat.Biproducts`, and
`import all Sheaf.Paper.IntegralSectionRegularScalars`. The private import of the existing
finite-presentation module exposes its already-proved ordinary-presentation API.
No other existing module or declaration interface is changed.

Validation: `lcompile.py --all` compiled both modules in 28.8 s and 32.3 s.
The one reported unused section variable was then explicitly omitted from the
private matrix-naturality theorem; the delivery checks recompile the final files.

## Proved and sorry left

Completed the private proofs `scalarFreeComparison_natural`,
`scalarPresentationComparison`, and `IntegralSectionScalars.finiteColimits`.

Closed the original body of
`AlgebraicGeometry.ProEtale.integralSectionScalarModels` (one original hole).
Added one hole:
`AlgebraicGeometry.ProEtale.IntegralSectionScalars.regularComparison`, in
`Sheaf.Paper.IntegralSectionRegularScalars`, attached to
`lem-sfb-integral-section-regular-scalars`.
The item itself has zero holes; the delivery has one hole. This is a decomposition,
with one hole closed and one added, not a net hole reduction or a completed proof
of the rank-one coefficient calculation.

The new theorem has neither an arbitrary module nor a finite-presentation
hypothesis. It isolates exactly the rank-one coefficient-normalization part of
step 1 of the original plan. The complete assembly from rank one to arbitrary
finite presentations is proved in this delivery. Zero ranks and rectangular
matrices are handled by biproduct universal properties; no torsion-free,
projectivity, nonempty-scheme or Noetherian hypothesis has been added.

## No longer needed

None of the original four dependency modules is pruned: all define the functors
or supply the finite-presentation/exactness results used here. No public import,
module, declaration or node is removed. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan combines a coefficient
normalization argument with a finite-presentation argument. This delivery
formalizes the latter and leaves only the former as an explicit rank-one item.
The new statement is strictly one step of that plan, not the arbitrary-module
comparison under a new name. Searches of the imported blueprint for regular
modules and scalar comparisons found no node stating this fixed rank-one
normalization square; the existing general regular-module APIs are its components.

Searches found no direct Mathlib comparison for these fixed functors. The
repository does contain `Mod.regularExtensionIso`,
`CondensedRing.sectionModuleRegularIso`, `CondensedRing.ringModuleUnitIso`, and
`IntegralModelsStacks.integral_constant_section_projection`. These supply useful
parts of the remaining rank-one proof, but their ring and realization expressions
still need to be connected to the exact composites in `regularComparison`.

## New nodes

`lem-sfb-integral-section-regular-scalars` records the scalar-compatible rank-one
comparison, its two-step proof in words, the original source, Mathlib search
results, the same chapter and unit, and its ancestry through
`lem-sfb-integral-section-scalar-models`. The original scalar-model node now
records the actual finite-biproduct matrix and preserved-cokernel proof, with the
new rank-one node as its only new proof dependency. No change record is needed:
only the item, its own node, and one new module/node are changed.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
