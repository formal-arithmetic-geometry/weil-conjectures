## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_finite_free_matrices_of_stalk_local`
in `Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteMatrixLift`, with its statement
and visibility unchanged. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` for the existing
free-sheaf matrix and pullback API. Every helper is private and fully proved.

The proof constructs scalar multiplication morphisms from global sections, realizes
matrices by finite sums of free inclusions, and proves matrix injectivity using
coordinate projections. It represents the dependent finite list of all coefficients
on one common open and compares the matrices after stalk pullback. The comparison
step uses naturality: the discrepancy between the two bases is a common scalar,
which commutes with every matrix over the commutative structure ring. This avoids
an explicit composition-coherence calculation for pullbackFreeIso.

Updated the existing DAG node's proof, proof_deps and proof_origin to match this route.
No definitions or statements of the existing library changed. No forced adaptations.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_finite_free_matrices_of_stalk_local`
(node `lem-pc-finite-free-stalk-finite-matrix-lift`).

Holes closed: 1. Holes added or split off: 0. Sorries left in the delivered module: none.
All scalar, matrix, finite-intersection and comparison helpers are proved.

The single-file Lean compile succeeds without warnings. The delivery dry run checks
the full module and its axiom probe. Empty coefficient families and zero ranks are
included: the finite infimum is top when empty, so the constructed neighbourhood
is V; finite sums and coordinate extensionality handle zero free sheaves.
The unit record `sk-thm-picard-perfect` has empty realized entries, and no unit
statement or proof step is bypassed or changed.

## No longer needed

The proof does not use node `lem-weil-pbc-spec-tilde-free-module`: global coefficients
come directly from freeMatrix and ΓSpecIso, and matrices are realized explicitly.
It was a planned dependency, not an import in the supplied module; it is removed
from this node's proof_deps. No target-closure module pruning is claimed.
No existing imports were removed. The two public imports remain necessary for the
unchanged statement; the only added import is used by the proof.
The presheaf-module stalk-functor module is not imported: the coefficient argument
uses Mathlib's structure-ring germ representation API directly.

## Where the brief, the DAG or earlier work was wrong

The planned tilde/free-module comparison is unnecessary. The planned explicit
unit-factor coherence computation is also unnecessary: naturality of the supplied
comparison and commutativity of endomorphisms of the unit suffice.
There is no statement error. The compiled snapshot initially lacked
StalkRestrictionWithinIso; work continued on independent helpers until the refreshed
snapshot supplied it. No dependency was copied or redeclared to work around this.

## Second reading by Y2

1. **Interfaces: pass.** Compared the complete module and node with the repository
   using diff. The sole existing theorem signature is byte-for-byte identical,
   including hypotheses, conclusion, universes and visibility. The only added
   import is proof-only. There are no interface changes or change records.
2. **Proof and axioms: pass.** Read all fourteen private helpers and the main proof.
   The module compiles without errors or warnings. A scratch copy with
   `#print axioms` for every helper (including both definitions) and the main theorem
   compiles; every declaration uses only `propext`, `Classical.choice`, `Quot.sound`.
   No sorry or prohibited declaration occurs. Scalar and matrix data are explicit
   constructions; germ representatives are chosen from Mathlib's proved theorem,
   with no arbitrary data taken from an unproved existence statement.
3. **Split statements: pass (none).** No holes or public statements were split off.
   The finite dependent coefficient family handles varying ranks; an empty family
   gives U=V, and zero rows or columns are handled by empty sums and free extensionality.
   The scalar comparison is valid even for an arbitrary natural comparison: naturality
   on inclusions gives the same unit endomorphism on every summand, and commutativity
   makes it central. All such claims are proved locally, not assumed.
4. **Route and pruning: pass.** Independently searched Lean Finder for the equivalence
   between free sheaf morphisms and matrices, Loogle for unitHomEquiv, and the local
   Mathlib/upstream/Sheaf sources for matrix injectivity, freeHomEquiv and germ lifting.
   freeHomEquiv describes compatible families of sections and does not supply the
   missing global-function matrix equivalence or simultaneous neighbourhood lift.
   The implementation already uses the existing unitHomEquiv, free projections,
   finite coproduct identities and freeMatrix_pullback. No shorter existing theorem
   was found. Both public imports serve the unchanged statement; the proof-only
   import supplies the matrix API. The sole removed old proof dependency,
   lem-weil-pbc-spec-tilde-free-module, is listed under No longer needed. No imported
   module or target-closure module is pruned. The unit's realized entries are empty;
   its finite-coefficient extension route and record are unchanged.
5. **DAG: pass.** Only proof, proof_deps and proof_origin differ in the node JSON.
   proof_deps is exactly the union of the proof steps' uses. The steps describe the
   actual normalization, finite germ lifting, explicit matrix construction and
   scalar-naturality comparison. No new nodes are needed.

Second reading changed only the main theorem's proof docstring to describe the
implemented scalar-naturality argument instead of the original proposed explicit
pullback-coherence calculation, and added this review report. No Lean proof needed
repair. Holes closed: exists_finite_free_matrices_of_stalk_local (1 of 1).
Holes added: none; split off: none. This is a proof, not a decomposition.
