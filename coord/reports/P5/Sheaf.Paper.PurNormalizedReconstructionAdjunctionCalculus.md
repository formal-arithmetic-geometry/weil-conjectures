## What changed

Filled the three proofs in `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`.
The reconstruction proof uses the actual normalized-system projection counit, finite
scalar adjunctions, and canonical Roos triangles. For a complete object, uniqueness
of the objects of two Roos triangles gives an object isomorphism to its reconstruction;
the triangle identity and naturality then prove invertibility of the actual unit.
The restricted unit and counit follow from the fully faithful inclusion formulas.
The final calculus uses adjoint-equivalence conjugation and naturality.
All existing declaration signatures, definitions and public imports are preserved.
The reconstruction DAG proof is updated to this route; no new node is introduced.

## Proved and sorry left

Closed: `WeilConjectures.purNormalizedReconstruction`,
`WeilConjectures.purRestrictedUnitCounit`, and
`WeilConjectures.purNormalizedReconstructionAdjunctionCalculus`.
Three original holes closed, zero holes added or split off, zero holes left in the item.
The proof uses existing named dependencies, including the existing
`WeilConjectures.normalizedDVR_kflat_transition`; their independent proof work is unchanged.

## No longer needed

Removed proof imports `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
`Sheaf.Paper.DerivedNakayama`, and the redundant direct import
`Sheaf.Paper.NormalizedDVRTower`.
The reconstruction proof no longer needs the declared dependencies
`lem-pur-kflat-change-of-rings`, `lem-pur-derived-change-of-rings`,
`lem-pur-roos-intrinsic-completeness-equivalence`,
`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients`,
`def-pc-perfect-ring-complex`, or `def-weil-pbc-adic-coefficient-datum`.
Normalization is already supplied by the input calculus; completeness is already
expressed by a quotient Roos triangle. Thus the extra intrinsic-completeness
conversion and its coefficient-ring verifications are unnecessary here.
The explicit dependency on `def-coef-normalized-dvr-tower` remains in the unchanged
statement dependencies and through effectivity, though it is not a separate proof step.
These are dependency removals for this item, not module withdrawals; other consumers
and unit routes are preserved. Removed top-level tool approvals are exactly the
obsolete dependencies named above; remaining approvals retain their order.

## Where the brief, the DAG or earlier work was wrong

The theorem docstring describes the older Nakayama argument. The reviewed DAG already
correctly warns that projections do not determine arbitrary maps into a homotopy limit.
This proof uses only an object isomorphism obtained from distinguished Roos triangles,
then unit naturality; it makes no such map-uniqueness assertion.
The generic Roos and K-flat transition tools used below the unit are
`lem-coef-sequence-roos-model`, `lem-coef-constant-tower-roos`,
`lem-coef-normalized-dvr-kflat-reduction-model`,
`lem-coef-normalized-dvr-kflat-transition`, and `lem-weil-derived-limit-existence`.
They implement the reconstruction step of `sk-thm-purity-transport`, without bypassing
any statement or proof step of that unit. No new tool approvals are written by the worker.
The independent reader can review these uses with the updated proof steps.
The required `lcompile.py` single-file check passed cleanly in 23.0 seconds.
The revised dependency union was checked against the proof steps; no new dependency
has a path back to the item. A broader traversal also encounters an existing cycle
between `lem-pc-ring-hom-extension-differential` and its adjacent-component lemma,
well below the already-used effectivity dependency; this delivery does not create it.

Preflight requested a change record for the local elaboration attribute commands:
`coord/changes/p5-reconstruction-local-attributes.md`. These controls are local,
and no importer-visible signature, definition or instance attribute changes.
The declaration-user check reports this item and
`Sheaf.Paper.IntegralSystemReductionFullyFaithful`; no adaptation is required.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
