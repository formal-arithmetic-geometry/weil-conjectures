## What changed

Proved `CategoryTheory.Functor.exactDerivedCohomologyCoherence` without changing its
statement. The short-complex composition identity
`CategoryTheory.ShortComplex.mapHomologyIso_comp` gives the inverse comparison
identity on cochain complexes. The compositor factorization equation and the
normalization of the derived homology comparisons reduce the derived composition
law to that identity, using naturality and localization extensionality. The
existing `mapDerivedCategoryHomologyFunctorIso_hom_app_naturality` supplies the
natural-isomorphism law; cancelling the compositor with its inverse finishes.

Added the proof import
`WeilConjectures.Algebra.Homology.ShortComplex.MapHomologyIsoComp`.
The existing four DAG proof dependencies remain the mathematical ingredients;
existing proved library lemmas implement the kernel/quotient and naturality
calculations of the plan. No new statements or definitions. The theorem uses scoped elaboration transparency
settings to identify the composite termwise functors; no global option changes.

## Proved and sorry left

Closed: `CategoryTheory.Functor.exactDerivedCohomologyCoherence`
(node `lem-pur-exact-derived-cohomology-coherence`), one of one holes.
Added holes: none. Remaining holes in the delivered module: none.

## No longer needed

Removed the direct proof import
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`; its declarations are
provided by the imported short-complex composition module. No mathematical DAG
dependency, node or module is withdrawn: the proof follows the existing route.
No source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The earlier searches missed the existing source-library composition law
`ShortComplex.mapHomologyIso_comp`, as well as the complete derived naturality
law `mapDerivedCategoryHomologyFunctorIso_hom_app_naturality`. These let the
proof reuse the existing kernel/quotient argument and the natural-isomorphism
descent without adding intermediate holes. The statement and unit route are
unchanged.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
