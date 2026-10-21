## What changed

Completed `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory_hom_fac`
in `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact`.
The proof installs the same right-derived and left-Kan-extension instances used in
constructing the comparison, then applies `Classical.choose_spec` to its defining
unique-existence theorem. This extracts exactly the required unit compatibility.
Statements, definitions, imports, and the DAG proof route are unchanged.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory_hom_fac`
(node `def-sfb-right-derived-exact`).
No holes remain in the item; no holes were added or split off.
The existing right-derived universal pair remains the stated dependency.

## No longer needed

None. The three existing public imports supply the definitions and instances used
by the comparison construction and proof. All recorded dependencies remain needed
by that construction; no nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The canonical comparison was already constructed from a unique-existence
statement including this equation. Its specification directly completes the final
step of the recorded proof, without a new intermediate result.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
