## What changed

Proved `AlgebraicGeometry.Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp`
in `Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite`, following the existing
four-step DAG proof. Mathlib supplies local finite-type cancellation, the isomorphic
diagonal of a monomorphism, the open and closed immersion instances for an
isomorphism, and separatedness. The definition of `IsUnramified` combines local
finite type with the open diagonal. The existing theorem
`Scheme.Hom.isLocallyQuasiFinite_of_unramified` gives the final two conclusions,
since the project's `IsLocallyQuasiFinite` is definitionally pointwise
`IsQuasiFiniteAtPoint`.

The existing public imports and the private proof import are used and retained.
No declaration signatures, definitions, or proof dependencies changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp`
(blueprint: `lem-trf-monomorphism-finite-type-composite-lqf`).
No holes remain in the item; no holes or modules were added or split off.

## No longer needed

None. The proof uses the existing dependency route, including the project's
unramified-to-affine-neighbourhood quasi-finiteness theorem. No nodes, modules,
or imports are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing Mathlib diagonal instance implements the categorical inverse
argument of step 2, and its separatedness instance implements step 3. The
pointwise conclusion is exactly the project's affine-neighbourhood definition,
not an identification with Mathlib's different quasi-finiteness predicates.
The unit route is preserved. No new statements or definition repairs are needed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
