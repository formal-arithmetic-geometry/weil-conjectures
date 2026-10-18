## What changed

Proved `AlgebraicGeometry.Scheme.indEtale_affine_strictLocal_baseChange` with its
signature unchanged. Four proved private helpers package pointed functoriality,
locality of evaluation, affine structural ind-etaleness, and the application of
Olivier to a pointed strict-local map. The final proof constructs the commuting
square, the pullback comparison isomorphism, its structural equation, and uniqueness.

The proof uses the existing `proAffineEtale` API for base change, composition and
cancellation instead of introducing tensor-product coordinate rings. Added proof-only
imports of `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`,
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`,
`Sheaf.Paper.StrictHenselizationPointEvaluationProperties`, and
`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`. All public imports and
all public declaration signatures are unchanged. Updated the existing node's proof,
proof dependencies, and proof origin to match this route.

The full proof and the final pruned file both compiled through lcompile.py in
5.5 seconds, with no warnings. The delivery tools check the final file again.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.indEtale_affine_strictLocal_baseChange`
(node `lem-weil-pbc-ind-etale-affine-strict-local-base-change`).
Added 0 holes; split off 0 statements. No `sorry` remains in any delivered Lean file.
The private helpers are fully proved. Existing imported theorems remain the
project's declared dependencies; this delivery does not claim their holes closed.

## No longer needed

Removed proof imports `Sheaf.RingTheory.IndEtaleStability` and
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`.
The bundled theorem `RingHom.indEtale_principalZariski_stability` and its node
`lem-weil-pbc-ind-etale-stability` are not needed by this proof: the source library's
proAffineEtale API provides exactly the composition, base change, cancellation, and
weak-etaleness clauses used here, without the principal-Zariski clauses.
The affine tensor-product comparison node `lem-weil-pbc-fibre-product-affine-spectra`
is also unnecessary: Mathlib knows the fibre product is affine, and the scheme API
handles its projection directly. No module realizing the unit's statement or proof
steps is bypassed. No global unreachability of these shared dependencies is claimed.
The standalone closed-lift factorization theorem is unnecessary because the unique
pointed-map interface supplies the exact evaluation equation used in the proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The original DAG's tensor-product
coordinate calculation is avoidable. Pointed functoriality's convenience interface
and the existing proAffineEtale scheme API express the same argument more directly.
Locality of the induced ring maps is established explicitly from pointed evaluation
rather than assumed from the convenience interface. Empty affine schemes cannot carry
the specified geometric points; no finiteness of A to C, or algebraicity restriction
on Ω, enters the proof. No definitions or target signatures were changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
