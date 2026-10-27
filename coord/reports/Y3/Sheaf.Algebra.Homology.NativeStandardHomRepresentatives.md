## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.nativeStandardHomRepresentatives` without changing
its statement. Added the private proof import `Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso`.
All construction and proof helpers are private in the item module.

The proof uses the existing homotopy-category equivalence of K-injectives with the derived
category. It constructs the source comparison with the actual native source representative
(the private source-comparison argument follows `SingleAssembly` in
`Sheaf.WeilSheaf.DerivedHomSingleResolution`). Target postcomposition is made into a functor,
with the row-sign target homotopy checked against product projections, and descended through
the homotopy quotient. Transport along the K-injective equivalence supplies the bifunctor.
Its unit isomorphisms and the source comparison give arbitrary-source representatives.
The slice isomorphism uses precisely `kInjectiveRep` and `kInjectiveRepIso`; its normalization
is proved by functoriality and the source comparison's native normalization.

Validation: the complete item compiled cleanly through `lcompile.py` in 23.1 seconds, with
no warnings. A direct comparison confirmed that the theorem signature is unchanged, and the
module contains no `sorry` tokens or lines over 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeStandardHomRepresentatives`
(`lem-sf-native-standard-hom-representatives`).
No holes remain in the item. No holes were added or split off.

## No longer needed

No imports, modules or declared dependency nodes were pruned. Both declared proof inputs
remain used: `lem-sf-native-hom-precomposition-quasi-iso` supplies source invariance, and
`lem-weil-pbc-kinjective-hom-derived` supplies the Mathlib homotopy-category bijection and
equivalence infrastructure. The proof does not need a new functorial complex-level target
replacement or a separate localization of the product category; the existing equivalence
already gives the required descent.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect was found. Replaced the planned explicit product
localization by transport through the existing K-injective homotopy equivalence and updated
the node proof accordingly. The unit route and all public interfaces are unchanged.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
