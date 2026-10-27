## What changed

Filled `AlgebraicGeometry.affineRelation_flat_local_descent` without changing its statement or
`affineRelationTensorComparison`. Added two proved private helpers for local faithful-flat
reflection of linear-map bijectivity and module flatness. Both use prime-localization tensors
as localization models and cancel the intermediate scalar extension before applying faithful
flat descent. The comparison is reinterpreted as an A-algebra homomorphism with the first-factor
A-action, so its inverse transports finite presentation of B to A tensor_C A. Faithful-flat
module descent then gives finite presentation of A over C.

The remaining clauses use finite-projective splitting, the existing standard-free-cover
result, the affine finite/flat/finite-presentation criteria, and pullbackSpecIso with its
projection identities. All public imports and public declaration signatures are preserved.
Only this item module and its own DAG node are changed. The node records the implemented
proof, including the shorter affine argument for finite local freeness.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affineRelation_flat_local_descent`
(node `lem-a1-affine-relation-flat-local-descent`).

No holes remain in the item and no holes or split-off statements are added. Both private
helpers have complete proofs. Existing imported statements remain the project's downstream
proof tasks; this delivery does not claim to close their holes.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum` and the corresponding
node `lem-weil-pbc-finite-free-algebra-spectrum` from this item's proof dependencies and
maintainer-approved tool list. Also removed `lem-weil-pbc-finite-local-on-target` from the
proof dependencies. Global module finite presentation gives module finiteness and algebra
finite presentation, so the affine criteria prove finite local freeness immediately, without
passing to the standard-free cover and gluing its scheme restrictions. The cover itself is
still constructed because it is an explicit conclusion of the theorem.

The separate planned dependency `lem-sc-affine-standard-cover-finite-free-local-fp-flat` is
also unnecessary: freeness alone implies flatness of D_p tensor_C A by the Mathlib instance.
The finite-presentation part of the given standard cover of B is still used through
`Module.finitePresentation_and_flat_of_finite_free_standard_cover`.

Also removed redundant direct proof imports of
`Mathlib.RingTheory.LocalProperties.Exactness`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, `Mathlib.Algebra.Module.Projective`,
`Mathlib.AlgebraicGeometry.Morphisms.Finite`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, and
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Their used declarations remain
available through the retained imports. The briefly added direct import of
`Mathlib.RingTheory.Localization.BaseChange` was likewise unnecessary.

These are prunings from this item's proof only; no library module or upstream declaration is
withdrawn. In particular other parents may continue to require these tools.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The planned chart argument for finite local freeness is
longer than necessary once global module finite presentation and flatness are established.
The proof does not need the injectivity assumption or finite-generation component of hlocal;
the original signature is retained. The zero ring, empty standard cover, and rank-zero module
cases use the same instance and localization arguments without a nontriviality assumption.
The arbitrary affine-open clause is proved for every C-algebra T, including the zero algebra.
No unit statement or unit proof step is bypassed: the node remains on the supporting affine
quotient branch, and the unit's realized statement and step lists are empty for this node.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
