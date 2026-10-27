## What changed

Proved `AlgebraicGeometry.etaleSystemEvaluationBound` without changing any existing
signature, record, definition or public import. The proof constructs the evaluation
isomorphism by conjugating the canonical insertion comparison under the composite
adjunctions, verifies its six Hom bijections and uniqueness, and proves all unit,
counit, coefficient-mate, actual-transition and uniform-bound clauses.

Added three comparison-normalization modules. `EtaleBrownEvaluationMate` proves the
open evaluation mate and the insertion/evaluation mate by localization on complex
representatives and mate pasting. `EtaleBrownSupportTransition` derives the actual
scalar-adjoint transition square from the recorded restriction-form image squares.
`EtaleBrownCoefficientCoherence` isolates the coefficient projection unit and cocycle.
Their statements are strictly parts of the original argument, independent of the
chosen system and finite exceptional right adjoints. Updated the DAG proof accordingly.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.etaleSystemEvaluationBound` (one of one).
The main module contains no `sorry`. All private helpers in the main module are proved.

`AlgebraicGeometry.etaleBrownEvaluationMate` is proved. The new theorems
`AlgebraicGeometry.etaleBrownSupportTransition` and
`AlgebraicGeometry.etaleBrownCoefficientCoherence` remain `sorry`, with nodes
`lem-pur-etale-brown-support-transition` and
`lem-pur-etale-brown-coefficient-coherence`. They are independent transition and
coherence results strictly below the original theorem. The original hole is therefore
reduced to these two separate results. No definitions, instances, private declarations
or anonymous proofs contain holes.

## No longer needed

No existing public imports were removed, and no modules are withdrawn.
The old explicit dependency `lem-weil-pbc-truncation-cohomology` is unnecessary:
`DerivedCategory`'s t-structure `isGE_iff_orthogonal` proves the bound directly after
the finite-adjunction Hom calculation. The direct Yoneda reconstruction dependency
`lem-galois-yoneda-fully-faithful` is replaced by `conjugateIsoEquiv`; the Hom-chain
and its uniqueness are checked explicitly. The main proof uses the existing scalar
adjunctions in its recorded packages, and the coefficient projection result through
the new normalized coherence statement; it does not separately invoke the original
coefficient-projection existence theorem. The dependency modules remain used where
the comparison normalization requires them. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan omitted the Lean glue
identifying the insertion mate with the specifically constructed evaluation and
transporting coefficient coherence through the normalized realization. These are now
explicit comparison lemmas. The unbounded lower-bound argument needs no prior bound
on the right adjoint and no assertion that evaluation is faithful on derived maps.
Repeated coefficient indices, zero objects, nonflat quotient maps and arbitrary
integers in the cohomological bound are all included in the signatures.

## New nodes

`lem-pur-etale-brown-evaluation-mate`: normalized open evaluation and compact-support
insertion/evaluation mates, proved by actual complex-representative comparisons.

`lem-pur-etale-brown-support-transition`: scalar-adjoint compatibility of actual
compact-support system transitions, obtained by transposing the recorded open and
proper image transition squares and pasting.

`lem-pur-etale-brown-coefficient-coherence`: unit and cocycle for the inverse canonical
coefficient projection through the canonical derived tensor associators. This is
precisely the coefficient-coherence part of Zheng Construction 5.15 and (5.16.2),
and does not repackage the evaluation-bound theorem.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
