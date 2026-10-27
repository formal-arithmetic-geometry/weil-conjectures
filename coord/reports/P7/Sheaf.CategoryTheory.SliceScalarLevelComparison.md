## What changed

Proved `SheafOfModules.exists_sliceScalarLevelComparison` in the assigned module.
The comparison is constructed from the normalized coefficient and slice-extension
Hom equivalences. Their common target is the Hom set into the scalar-restricted
slice module. Naturality supplies inverse maps; evaluating the transposes and
using module linearity proves the full generator formula. The same injectivity
proves uniqueness. The already proved `RingedOpenScalar.comparison` supplies the
scalar identification. Presentation equations prove all transitions and naturality.
Private proof imports of `Sheaf.CategoryTheory.RingedOpenScalarAdjunction`
and `Sheaf.CategoryTheory.SliceScalarLevelAdjunction` are added. The existing
comparison data is moved verbatim (apart from its node references) into `SliceScalarLevelComparisonBasic`, which is publicly re-exported.
Existing public signatures, definition bodies and imports are preserved. This
separates expensive structure generation from the proof to satisfy the 60-second
per-file limit; private comparisons are irreducible after their API is proved.
The node proof now records this adjunction route. The sole citer
`lem-sf-semilinear-slice-scalar-generators` retains exactly the same use of the
existence theorem; the added statement dependency identifies the relocated data.

Validation: all three delivered files compiled without warnings, in 27.7 seconds
(adjunction), 31.2 seconds (data) and 34.0 seconds (item). The sole direct importer,
`Sheaf.CategoryTheory.SemilinearSliceScalarGenerators`, compiled unchanged against
the delivery in 15.3 seconds; its temporary copy was removed from the packet.

## Proved and sorry left

Closed the one existing hole:
`SheafOfModules.exists_sliceScalarLevelComparison`
(node `lem-sf-slice-scalar-level-comparison`).
No holes added or split off; no `sorry` remains in the three delivered Lean files.
All helpers are proved. The generic support module adds the proved
`SheafOfModules.exists_scalarSliceAdjunctionComparison` and
`SheafOfModules.scalarSliceAdjunctionHom_ext`; its construction helpers are private.

## No longer needed

No existing imports removed and no modules withdrawn. The proof does not use the
planned local-section argument, so `lem-pc-sites-sheafification-underlying-sets`
and `lem-weil-pbc-site-sheafification-sections-local` are removed from this node's
proof dependencies. The ordinary comparison theorem
`SheafOfModules.exists_ringedSliceTensorGenerators` is not used: the coefficient
comparison follows directly from the two adjunctions. Its module and node remain
needed for `ringedSliceExtensionSection`, the shared original-generator definition,
and remain in the dependency record for that use. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's local generator/linearity construction was
longer than necessary: normalized Hom equivalences produce coefficient-linear
maps from the start and detect equality on unit tensors of original summands.
This replaces the planned ordinary-tensor comparison and local-refinement proof.

## New nodes

`def-sf-slice-scalar-level-comparison-data`: the existing component transport
and comparison structure, relocated unchanged to
`Sheaf.CategoryTheory.SliceScalarLevelComparisonBasic`. No new mathematical
obligation and no hole. The original node keeps its existence theorem and gains
this statement dependency.

Change record: `coord/changes/P7-slice-scalar-level-comparison-layout.md`.

`lem-sf-slice-scalar-adjunction-comparison`: the fully proved generic scalar/slice
comparison and unit-tensor Hom extensionality criterion, with no tower or
coherence data. Its construction and the tower coherence proof are checked in
separate modules. No hole is introduced.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
