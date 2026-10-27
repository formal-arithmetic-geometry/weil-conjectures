## What changed

Proved `AlgebraicGeometry.Etale.etaleSumScalarRepresentative` by formal adjunction comparison. The private helpers establish composition of the unit-transpose comparisons and compatibility with conjugate transformations. The exact-derived unit formula identifies the sum comparison with the published exact factor; the scalar comparison is the defining scalar representative. The ordinary uniqueness isomorphism and the specified derived conjugate then give the displayed map equality. Added a private proof import of `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`. No public signature or definition changed. The full proof compiled on the server in 52.8 seconds with profiling enabled after the scalar unit formula was normalized in the general helper. The final code also fixes the generic complex-map endpoints explicitly and removes the development profiling options. The large ordinary sheaf functors are locally irreducible during specialization.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Etale.etaleSumScalarRepresentative` (node `lem-sp-etale-sum-scalar-representative`). Added zero holes. No `sorry` remains in the delivered module. Every private helper is proved.

## No longer needed

The planned bounded-flat/K-flat computation and `Etale.preservesFlat_etaleLowerShriek` from `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection` are unnecessary for this morphism equality: the scalar representative is defined by adjunction for every complex. The proof dependency `lem-pur-derived-change-of-rings` is replaced by the precise existing representative-definition node `def-sp-coefficient-scalar-representatives`; no theorem about derived tensor computation is applied. These modules may still be required by other parts of the library. No existing public import was removed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan unnecessarily sought invertibility of the representative arrows. Equality is formal before imposing boundedness or flatness, so the unchanged theorem follows after discarding those hypotheses. The node proof and proof dependencies now record this route. The unit route remains unchanged.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
