## What changed

Proved both theorems of `Sheaf.AlgebraicGeometry.AffineFiniteModuleFreeLocus`, with their
signatures and public imports unchanged. Added proof-only imports of
`WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.

The module-cover theorem first obtains finite presentation over the Noetherian ring,
then uses Mathlib `Module.freeLocus_eq_univ_iff` to obtain projectivity and the source
library's proved `Module.exists_standardFreeCover_of_finite_projective` to obtain the
cover. The sheaf theorem transports the hypothesis to global sections using
`tilde.isoTop`, applies the first theorem, and uses the proved localization-to-free-sheaf
comparison and cover criterion. A universe lift of `Fin n` supplies the required index
universe without changing the cover. Updated the node proof, dependencies and origin.

The local-projectivity node `lem-trf-finite-projective-local-free` is a Mathlib leaf;
`lem-weil-pbc-finite-projective-standard-free-cover` is Lean-closed. They are generic tools,
so this does not replace any step of the Riemann--Roch unit. Its realized arrays impose
no additional route through this auxiliary node.

Validation: the complete module compiled on the project server in 3.5 seconds.
No definitions, statement signatures, visibility, or existing public imports changed;
no consumer adaptations or change records are needed. The delivery gate also checks
axioms and the hole census.

## Proved and sorry left

Closed two holes, both on `lem-sc-affine-finite-module-free-locus`:

- `Module.finite_free_at_primes_localized_cover`.
- `AlgebraicGeometry.isFiniteLocallyFree_tilde_of_free_at_primes`.

Holes added: zero. Holes remaining in the delivered module: zero. Split-offs: zero.
The existing source lemmas used for the proof are proved; no assumed theorem is used.

## No longer needed

No imports removed and no whole module pruned. Both added proof-only imports are used.
The direct dependency `lem-sc-finitely-presented-free-at-prime-principal` is replaced by
the already proved standard-cover theorem, whose proof performs the same spreading
argument. That fact remains used transitively, so no global pruning of its Mathlib
module is claimed. The remaining original dependencies are still used, including the
principal-open criterion in the sheaf cover and the module-sheaf sections dictionary.
No sheaf-level projectivity criterion or additional intermediate module was needed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original plan can be shortened because the existing
source standard-cover theorem already combines pointwise spreading with compactness.
The free-locus equivalence additionally requires an explicit finite-presentation
instance; `Module.finitePresentation_of_finite A M` supplies it. All original hypotheses,
including the independent module universe in the first theorem, are preserved.
The construction allows the zero module, the zero ring, and empty finite covers;
it assumes neither a fixed rank nor nontriviality of A.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
