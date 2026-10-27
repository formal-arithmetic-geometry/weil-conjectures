## What changed

Filled `AlgebraicGeometry.universallyCatenary_of_affineOpenCover` in
`Sheaf.AlgebraicGeometry.UniversallyCatenaryAffineCover`, without changing its signature
or any public import. Added the private proof import
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.

For an affine open V and a finite type algebra A over its section ring, compose
Spec A → Spec Γ(X,V) with the affine-open immersion into X. Index the refining cover
by all pairs consisting of an original cover index and an affine open of Spec A
contained in its inverse image. The affine neighbourhood basis proves this is a cover.
The finite-type affine-pair criterion and the hypotheses make its section rings
catenary; the existing catenary-cover theorem makes Γ(Spec A,top) catenary.
Transport across Γ(Spec A,top) ≅ A finishes the argument. Noetherianity follows from
Mathlib's `IsLocallyNoetherian.component_noetherian`.

The proved private helper `catenary_equiv` transports finite prime-chain bounds and
saturation through the ideal order isomorphism of a ring equivalence. Its proof follows
the existing private helper in `Sheaf.RingTheory.IsExcellentFiniteTypeLocalization`;
that module is not imported, avoiding its unrelated excellence dependencies.

The proof follows Stacks Morphisms Tag 02J9, implication (4) implies (3), using the
stated Tag 02IX affine-cover theorem. The existing node's proof and dependencies
already describe this route, so no DAG update is necessary.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.universallyCatenary_of_affineOpenCover`
(node `lem-trf-universally-catenary-affine-cover`).

Added 0 holes and split off 0 statements. No sorry remains in the delivered module.
The existing imported theorem
`AlgebraicGeometry.isCatenaryRing_of_affine_openCover`
(node `lem-trf-catenary-affine-open-cover`) remains an external proof dependency.

## No longer needed

None. No imports removed, no declared dependencies bypassed, and no modules withdrawn.
The existing unit route is preserved. Mathlib directly supplies the finite-type,
open-immersion, composition, and affine-neighbourhood steps named in the DAG.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The construction handles empty schemes
and empty covering families without choosing a global cover index: membership in the
refining cover is proved pointwise. No new statement or definition was introduced.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
