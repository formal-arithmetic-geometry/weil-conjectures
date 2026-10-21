## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.bounded_finiteModel_generation`
without changing its statement. Private proved helpers define and manipulate finite
construction certificates, concatenate certificates for extensions, append shifts,
and interpret each certificate in the given triangulated class.

The sheaf case applies `exists_finiteModelStratumFiltration`, evaluates its natural
cokernel isomorphisms, and uses the degree-zero short-exact-sequence distinguished
triangles. The bounded-complex case reuses the proved source-library theorem
`DerivedCategory.prop_of_bounded_of_degreewise` instead of rebuilding its finite
Postnikov induction. A final zero shift makes the endpoint the last tuple entry.
The node's proof and proof dependencies follow this implementation.

All original public declarations and statements are preserved. No source-library
module is changed. The unit's statement and realized steps are preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.bounded_finiteModel_generation`.
Added 0 holes. Split off 0 statements. No `sorry` remains in the delivered module.
Every private helper is proved. This is a proof, not a decomposition.
The final module compiled through `lcompile.py` in 6.8 seconds (exit code 0).
A byte-for-byte comparison confirms that the public theorem signature is unchanged.

## No longer needed

Removed the direct proof imports
`WeilConjectures.CategoryTheory.TruncationTriangle` and
`Mathlib.Algebra.Homology.Embedding.CochainComplex`, and
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`; the latter's needed degree-zero
API is imported through `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.
The implementation no longer directly needs
`lem-weil-pbc-truncation-cohomology` or `lem-weil-pbc-truncation-triangle`:
the already proved `lem-sfb-degreewise-bounded-devissage` supplies the whole finite
cohomological induction. Removed the obsolete top-level tool-use approval for
`lem-weil-pbc-truncation-triangle` from this node. These declarations and modules
remain in the library; no global unreachability or withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooked the existing proved bounded degreewise devissage in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
The finite-model filtration returns cokernels of natural transformations rather
than a ready-made objectwise short exact filtration; evaluation preserves cokernels
and supplies the required bridge. No mathematical statement repair was necessary.

The first preflight to reach the server required a change record for the new
scoped private-helper section and flagged a private instance as global. The
instance is now proof-local. The scoped helper commands and their lack of public
interface effects are documented in
`coord/changes/bounded-finite-model-generation-private-proof-helpers.md`.
The downstream check reports zero importing modules.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
