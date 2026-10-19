## What changed

Proved `AlgebraicGeometry.Scheme.relativeFrobenius_finite` in
`lean/Sheaf/AlgebraicGeometry/RelativeFrobeniusFinite.lean`, with its signature unchanged.
Two proved private helpers establish naturality of the n-fold absolute Frobenius and its
integrality. The latter uses the explicit monic polynomial `T^(p^n) - C(s)` for each section.
The relative morphism is constructed by `pullback.lift`; its integrality follows by
`IsIntegralHom.of_comp` against the affine, hence separated, first projection. Its finite
type follows by `locallyOfFiniteType_of_comp` against the second projection, and the
finite/integral/locally-finite-type criterion concludes. Pullback extensionality proves
uniqueness.

Updated `dag/nodes/sec-six-functors/lem-trf-relative-frobenius-finite.json` only in
`proof`, `proof_deps`, and `proof_origin` to record this shorter argument. No definitions,
existing signatures, public imports, or consumers change. No change record is required. The final single-file compile passed without warnings
(2.6 seconds); the required delivery dry run checks the final import-pruned file as well
as declaration signatures and axioms.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.relativeFrobenius_finite`
(node `lem-trf-relative-frobenius-finite`).

Added 0 holes. Split off 0 statements. No `sorry` remains in the delivery.
The private helpers `frobenius_naturality` and `frobenius_integral` are fully proved.
This is a proof, not a decomposition into further assumed statements.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism`
and `Mathlib.AlgebraicGeometry.Morphisms.Integral`; the latter is redundant because the
existing public `Mathlib.AlgebraicGeometry.Morphisms.Finite` import already imports it.
The proof no longer needs node `lem-trf-relative-frobenius-universal-homeomorphism` or that
module: direct integrality of the absolute iterate and separated cancellation avoid the
one-step relative theorem. It also does not need node
`lem-weil-pbc-closed-immersion-integral-separated-uc` (integral composition), or successive
Frobenius twists and their associativity isomorphisms. No other imports were removed.
Pruning is local to this item; the one-step module may still have other consumers.

The replacement uses existing Mathlib-leaf nodes
`lem-weil-pbc-affine-morphism-permanence` and
`lem-weil-pbc-integral-of-comp-separated`. The finite-type cancellation and finite iff
integral plus locally finite type nodes remain needed. There are no new nodes or new
unproved dependencies. The unit record has no realized statement or step assigned to
this node, so this change is entirely below the unit's fixed route.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The earlier five-step plan is valid,
but its iteration construction is unnecessary: an absolute power map is directly integral,
and its affine base-change projection is separated, so cancellation proves relative
integrality for every n at once. This works for empty schemes and zero section rings,
nonreduced schemes, non-quasicompact schemes, and bases whose absolute Frobenius is not
finite; only affineness of that Frobenius is used. The proof in fact also works for n=0,
while preserving the given n>=1 signature exactly.

Searches retained from the interrupted session found no matching generic relative-finiteness
theorem (LeanFinder) and found `IsIntegralHom.of_comp` (Loogle). A fresh grep for
`relativeFrobenius|relative_frobenius` in Mathlib AlgebraicGeometry returned no hits. Reading the existing source
library confirms its finite-field absolute-Frobenius finiteness result does not directly
cover this arbitrary-base statement. The DAG's existing cancellation Mathlib leaf supplies
the shorter argument.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
