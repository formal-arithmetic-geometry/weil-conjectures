## What changed

Completed `AlgebraicGeometry.ringComplex_cech_scalar_model` without changing its statement.
The proof chooses one finite generating list of I, proves its explicit ordered model K-flat
from boundedness and localization flatness, and transports its augmented derived comparison
to P through a K-flat common roof. The augmentation equation is preserved by first refining
it to a homotopy and then applying the additive scalar-extension functor.

Added `Sheaf.Paper.RingComplexScalarAugmentation`: its three definitions construct the unit
multiplication and augmented scalar extension from the existing semilinear adjunction. The
pure-tensor normalization theorem is proved. Added `Sheaf.Paper.RingComplexOrderedScalarIso`:
the explicit cochain comparison uses tensor over finite products and Mathlib's
localization tensor instance and `IsLocalization.algEquiv`. Localization uniqueness proves
the face squares, and linearity preserves the alternating differentials. No data is chosen from an existence
statement. The original theorem then uses the existing Godement model to compare every
generating list of J through the same augmented derived object.

The private bounded-flat and roof arguments follow the already proved arguments in
`GlobalSectionScalarCechModel`; they are specialized here without importing its unrelated
global-section extension construction. All new proof imports are private imports. No
existing module other than the item is changed. The existing public imports are preserved.

Validation: `lcompile.py --all` compiled all three delivered modules without warnings,
exit code zero. The final main-module compile took 18.1 seconds; the explicit scalar
comparison previously compiled in 17.5 seconds. Both are below the per-file limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ringComplex_cech_scalar_model`
(`lem-weil-pbc-ring-complex-cech-scalar-model`).

Also proved the new theorems
`AlgebraicGeometry.ringComplexScalarAugmentation_one_tmul` and
`AlgebraicGeometry.ringComplex_ordered_scalar_iso`. No holes are added or left in this
packet. The canonical augmentation definitions contain no holes. Thus this is one original
hole closed, zero split off, and zero remaining textual holes in the delivered modules.
The proof uses the project's existing dependency declarations in the usual stage-3 sense.

## No longer needed

No existing import is removed and no existing module is withdrawn. No dependency can be
claimed globally pruned. The original node's separate common-refinement construction for
changing generating lists is unnecessary here: the existing
`lem-weil-pbc-ring-complex-godement-cech` compares every list to one Godement object.
`lem-weil-pbc-localization-base-change` moves from a direct dependency of the item to the
explicit cochain-isomorphism node; it is retained. The K-flat, bounded-flat, localization
flatness, and K-flat change-of-rings dependencies are retained where used.
`def-pc-tensor-complex-sheaves` is used through the K-flat interface and remains an indirect
dependency; the item needs no additional direct tensor-complex lemma.

## Where the brief, the DAG or earlier work was wrong

No false statement or target-definition discrepancy was found. The plan's three substantive
steps are all implemented. The previously repeated scalar-model obligation is not split off
again: the explicit scalar cochain isomorphism, augmentation normalization, and roof argument
are proved. The Godement comparison already in the library supplies generator independence.
Empty generating lists, zero generators, and zero rings require no additional hypotheses:
finite tensor-product equivalences include empty index sets, and localization base change
includes localization at zero.

## New nodes

`def-weil-pbc-ring-complex-scalar-augmentation` records the constructed unit multiplication,
single-complex map, scalar augmentation, and its proved normalization. It introduces no
existence choice and no hole.

`lem-weil-pbc-ring-complex-ordered-scalar-iso` records the proved cochain isomorphism between
scalar extension of explicit ordered coordinates and the coordinates for the image list.
It has no derived-category, K-flatness, ideal, replacement, or generator-independence premise.
Its entire proof is included; it is not a renamed model obligation.

Change record: `coord/changes/ring-complex-scalar-augmentation-N2.md`.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
