## What changed

Proved `WeilConjectures.RationalSmoothPurityCanonical.rationalIntegralSource_eq`
in `Sheaf.Paper.RationalSmoothPurityCanonical` using the published object
specifications of rational tensor and rational pullback. After passing to integral
representatives, the tensor inputs coincide: the nonnegative signed Tate line is
the positive tensor power used by `twist`.

A proved private helper identifies the ambient object of an inherited
full-subcategory shift. Its proof unfolds the shift in an abstract category,
avoiding that expansion in the large coefficient presentation. The rational shift
comparison itself remains the original localization `commShiftIso`.

Updated the canonical-realization node's proof and dependencies. No public
signature, definition body, or import changes. No definition or statement change
record is needed. The original library and M2's category transport repair are
preserved.

`ordinaryTensor_eq` directly projects the tensor specification, with its two
presentation definitions transparent locally. The original global transparency and instance settings are preserved. Local
opacity for isomorphism composition, derived-functor constructions, and the chosen
left adjoint matches the existing settings in PuritySourceTransports; backward
use of the library's definitional-equality lemmas is enabled. The private-module style
scan is disabled for this intentionally public module: profiling measured
25.4 seconds in that scan alone. No development profiler settings remain.

Validation: remote `lcompile.py` completed with no errors or warnings in 55.7 seconds.


## Proved and sorry left

Closed 1 of the original 8 holes:

- `WeilConjectures.RationalSmoothPurityCanonical.rationalIntegralSource_eq`.

Added holes: none. No decomposition or split-off statement is introduced.

The remaining 7 holes, unchanged and all attached to
`def-pur-canonical-rational-purity-realization`, are:

- `WeilConjectures.RationalSmoothPurityCanonical.finiteIntegration_smoothPurityMap`.
- `WeilConjectures.RationalSmoothPurityCanonical.orientation_existsUnique`.
- `WeilConjectures.RationalSmoothPurityCanonical.smoothPullAugmentation_isIso`.
- `WeilConjectures.RationalSmoothPurityCanonical.smoothPullToOrdinary_existsUnique`.
- `WeilConjectures.RationalSmoothPurityCanonical.projection_isIso`.
- `WeilConjectures.RationalSmoothPurityCanonical.integralMap_isIso`.
- `WeilConjectures.RationalSmoothPurityCanonical.rationalIso_scalar`.

The source proof uses the existing rational tensor and pullback object
specifications, including their existing obligations. This is a partial delivery.

## No longer needed

No existing import, node, or module is pruned. The original dependencies still
serve the unchanged constructions and obligations. No new proof import is needed
for the delivered proof. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The rework table still names archived coefficient-model transport timeouts.
The current source already contains M2's restoration and category transport
repair; this delivery preserves it and makes additional proof progress.

The source equality does not follow by bare `rfl`: Mathlib intentionally marks
the inherited full-subcategory shift irreducible. The generic ambient-object
formula supplies the required equality. No rational shift is identified with an
integral shift: the original localization comparison remains in
`rationalSourceComparison`.

A development proof of `smoothPullToOrdinary_existsUnique` typechecked, but
versions carrying its additional localization imports exceeded the file's
60-second limit. It is not included or counted as proved. Its route is to use
`integralOperationsGoodLocalization_isLocalization` from
`IntegralOperationsWellDefined` via a private `import all`, descend the strict
augmentation by fully faithful precomposition, prove its components invertible
on the finite-Tor domain using `smoothPullAugmentation_isIso`, and invert.
Naturality gives the formula for every presentation, and one good representative
proves uniqueness. The integral residue-Tor equality supplies closure of the
domain under isomorphisms. Using the literal ordinary pullback functor from the
conclusion, with its pro-etale derived-category instances fixed locally, reduced
the new theorem's kernel checking from about 19 seconds to about 2 seconds, but
the complete module still exceeded the limit. The delivered file retains that
original obligation.

For the delivered equality, dimension zero and zero or empty-scheme inputs
require no extra hypothesis; the nonnegative twist clause includes zero.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
