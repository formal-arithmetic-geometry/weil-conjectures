## What changed

Filled `AlgebraicGeometry.Etale.supportedCoefficientTensor_openSecond` in
`Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor`. Both coefficient-map
definitions and the theorem statement are unchanged. All added helpers are private and
proved; all added imports are private proof imports. The change record
`coord/changes/W2-supported-second-open-tensor-proof-context.md` documents the added
private-helper scope commands and explicitly local elaboration attributes required by
the static preflight gate; no public mathematical interface changes.

The proof uses the ordinary second-open coefficient square and its signed-total-complex
square, as in the existing DAG. It identifies the specified projection comparisons and
open support mate with exact-derived natural transformations. A generic localization
calculation then descends the complex square, using a flat resolution in the second
variable so that the target localization tensor comparison is invertible. Naturality
transports the result from these models to arbitrary unbounded derived objects. The
pullback tensor comparison is normalized first on homotopy complexes and then on cochain
complexes. Flatness preservation for the supported coefficient functor is proved using
stalks and the open/closed decomposition. A private natural transformation uses the
canonical pullback tensor-isomorphism components directly; its naturality and
normalization follow from the transported tensor comparison. Local instance priorities
align the symmetry projection with that used by the generic coefficient API.

Validation: the complete item compiled through `lcompile.py` in 47.5 seconds, with no
errors or warnings, using the unchanged default limits.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.supportedCoefficientTensor_openSecond`
(node `lem-pur-supported-coefficient-second-open-tensor`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. No statement was split off.

## No longer needed

None. The original public import is retained. All five existing proof dependencies are
used, and the ordinary-square, signed-total-complex, and derived-normalization route of
the unit is preserved. No existing module, declaration, or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The existing planned route suffices. Explicit
generic conversion lemmas are needed to avoid expensive unfolding of the concrete sheaf
and signed-total-complex instances during elaboration; they do not change any definition
or public interface.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
