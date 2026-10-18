## What changed

Proved `AlgebraicGeometry.geometricallyReduced_of_generic_stalks`, keeping its signature,
visibility and existing docstring unchanged. Three proved private helpers implement tensor-coordinate
naturality for jointly injective families, closure of an affine irreducible component in the ambient
scheme, and reducedness of the tensor product from minimal-prime stalks. The proof then uses the
pullback of the affine open cover, the stalk isomorphism of an open immersion as a k-algebra
isomorphism, and `pullbackSpecIso`.

Added the proof-only import `Mathlib.LinearAlgebra.TensorProduct.Basis`. Updated the existing node's
proof, proof dependencies and proof origin to match the actual argument. No public definition or
statement changed; no consumer adaptation or change record is needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.geometricallyReduced_of_generic_stalks`
(node `lem-pur-geometric-reducedness-from-generic-stalks`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the item or is added elsewhere. The file compiles;
`#print axioms AlgebraicGeometry.geometricallyReduced_of_generic_stalks` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The private helpers
`tensor_reduced_of_jointly_injective`, `closure_image_component`, and
`tensor_reduced_of_minimal_stalks` are proved entirely from Mathlib.

## No longer needed

Removed the proof-only import `Mathlib.RingTheory.KrullDimension.Zero`; the proof uses no
Krull-dimension calculation. Removed `lem-weil-pbc-minimal-prime-reduced-localization-field` from the
node's proof dependencies: if a section maps to zero in a prime localization, the localization
membership criterion already puts it in the prime. Proving that the generic stalk is a field or that
its maximal ideal vanishes is unnecessary. No Sheaf module is withdrawn. All other declared
dependencies remain used: minimal-prime/irreducible-component correspondence, affine stalk
localization, prime containment and the nilradical characterization, a vector-space basis, affine
fibre products, open-immersion base change, and reducedness/geometric-reducedness definitions.

The finite coefficient-span construction is replaced by the existing
`TensorProduct.equivFinsuppOfBasisRight` for a full basis of the extension field. Its naturality is
proved by tensor induction, so no extra finite-span or basis-extension lemma is needed. The public
imports are preserved, including the existing compatibility re-export of the upstream presheaf
stalk functor, to keep the module's public interface unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned field-stalk calculation in step 2 is stronger than needed. Localization membership and
the intersection-of-primes characterization suffice. The rest of the route is retained. The
statement handles arbitrary reduced schemes, infinitely many components and the empty scheme;
there is no added finiteness or nonemptiness assumption. The canonical algebra compatibility in the
hypothesis is used explicitly through `stalkMap_toStalk` and composition of stalk
maps, so the proof does not replace the structure morphism by an unrelated algebra structure.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
