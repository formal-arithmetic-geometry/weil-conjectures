## What changed

`completedAdic_slice_scalarComparison` is proved by uniqueness of left derived
functors (`Functor.leftDerivedNatIso`). The ordinary comparison
`completedAdic_slice_scalarComparison_underived` is mapped to homotopy categories
(`NatTrans.mapHomotopyCategory`) and localized, giving the isomorphism of the two
localized ordinary composites; `completedAdic_slice_scalarComparison_derived_data`
supplies the two counits exhibiting the derived composites as left derived functors.
The slice definitions `completedAdicSliceChangeData` and
`completedAdicSliceDerivedChange` moved verbatim to
`Sheaf.Paper.CompletedAdicSliceScalarComparisonData` (publicly re-exported), with the new
`completedAdicSliceChange` and instance `completedAdicSliceChange_additive`.

(Reviewer FIX, 2026-10-28: the delivered `derived_data` took the ordinary comparison as a
hypothesis and returned the induced isomorphism `G ≅ G_U` as a conjunct, a trivial
consequence of the hypothesis; that step is now proved in the item and `derived_data`
states only the two left-derived-functor properties.)

## Proved and sorry left

`AlgebraicGeometry.Scheme.completedAdic_slice_scalarComparison` is proved from two
named lower statements, each a public `:= by sorry` with its node:

- `completedAdic_slice_scalarComparison_underived`, node
  `lem-weil-pbc-completed-adic-slice-scalar-comparison-underived`;
- `completedAdic_slice_scalarComparison_derived_data`, node
  `lem-weil-pbc-completed-adic-slice-scalar-comparison-derived-data`.

No definition contains a `sorry`.

## No longer needed

The item proof no longer uses lem-pc-kflat-resolution,
lem-weil-pbc-ringed-pullback-preserves-kflat or def-pur-localized-ringed-site directly;
they are used by the derived-data node.

## Where the brief, the DAG or earlier work was wrong

The previous delivery (2d8a) left a `sorry` inside the target proof. The item node's
owner records were stale after the definitions moved: the moved definitions are now
recorded by def-weil-pbc-completed-adic-slice-scalar-extension, which the item node cites.

## New nodes

- `lem-weil-pbc-completed-adic-slice-scalar-comparison-underived`: ordinary tensor/sheafification step.
- `lem-weil-pbc-completed-adic-slice-scalar-comparison-derived-data`: K-flat, restriction and counit step.
- `def-weil-pbc-completed-adic-slice-scalar-extension`: owner of `completedAdicSliceChangeData`, `completedAdicSliceChange`, `completedAdicSliceDerivedChange`.
- `def-weil-pbc-completed-adic-slice-scalar-extension-additive`: owner of the instance.

The interface change is recorded in `coord/changes/CompletedAdicSliceScalarComparisonData.md`.

## Related modules compiled before delivery

Direct importer Sheaf.Paper.FiniteQuotientModelResidueComparison: OK (deliver3.py, and
again by the reviewer against the corrected files, 25 s).

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
