## What changed

Proved `AlgebraicGeometry.Scheme.integralConstantRealization_exact_derived` in
`Sheaf.Paper.CompletedRealizationDerivedCohomology` by using the already proved
`integralConstantModule_exact` and existing `integralConstantModule_additive` instance.
After installing finite-limit and finite-colimit preservation and the standard derived
category of modules, the last two clauses are Mathlib instances for `mapDerivedCategory`
and `mapDerivedCategoryFactors.hom`, respectively. The constructions of the normalized
factorization, homology comparison and shifted-module comparison are preserved verbatim.
Validation: the final import-pruned module compiles cleanly with `lcompile.py` (2.8 s).
All declaration signatures and public imports are unchanged. Updated the theorem's
proof docstring and the node's proof, proof dependencies and proof origin to match.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.integralConstantRealization_exact_derived`
(node `lem-weil-pbc-completed-realization-derived-cohomology`).
Added 0 holes; split off 0 statements; no sorry remains in the item.
The proof uses existing exactness results rather than introducing any new assumption.

## No longer needed

Removed unused private proof imports:

- `Sheaf.CategoryTheory.FiniteTypeConstantExact`
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Localization.Predicate`

The first three modules are unnecessary as direct dependencies here: exactness of the
actual normalized realization is already proved in `IntegralStratifiedPerfectModels`.
The last two are available through the exact-functor construction's existing imports.
No module is withdrawn and no claim is made that these modules are globally unreachable.

Removed direct proof-dependency nodes:
`lem-weil-pbc-finite-type-constant-exact`, `def-weil-pbc-proetale-site`,
`def-sf-site-constant-module-functor`, `lem-weil-pbc-completed-constant-sheaf-reduction`,
`def-pur-sheaf-tensor-product`, `def-pc-sheaf-restrict-scalars`,
`def-weil-sheaf-of-modules-category`, and `def-weil-abstract-derived-category`.
Their relevant constructions or properties are already packaged in the unchanged realization
module. Statement dependencies are preserved. The complex cohomology, exact derived
factorization and localization nodes remain to describe the actual comparison constructions.
The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned proof repeated exactness of the realization even though
`integralConstantModule_exact` now proves it for precisely this functor. Using that API
avoids repeating constant-sheaf and completed-scalar arguments. The existing Mathlib
shift compatibility instance is exactly the last conjunct; no extra coherence lemma or
choice of comparison is needed. No mathematical statement or definition was repaired.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
