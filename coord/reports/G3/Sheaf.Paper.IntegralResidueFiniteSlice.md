## What changed

Proved `AlgebraicGeometry.Scheme.integralResidueFiniteSlice` without changing its
statement or definitions. Added proof-only `import all` access to the proved private
helpers in `Sheaf.Paper.IntegralResidueFiniteReduction` and
`Sheaf.Paper.PerfectChartTensorComparison`. The first comparison transports the
finite inverse-image isomorphism to raw datum-ring pullback; the second identifies
that pullback with the actual derived slice. Scalar restriction commutes with slice
restriction definitionally. Exact derived factorization and the canonical
localization representative isomorphisms give the required normalized endpoints.
Updated only the item's node proof, proof dependencies, and proof origin.

The item compiled cleanly through `lcompile.py` in 17.0 seconds. The proof applies
to all given complexes and all n; it introduces no bounds, nonemptiness conditions,
perfectness assumptions, or additional coefficient hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.integralResidueFiniteSlice`
(node `lem-weil-pbc-integral-residue-finite-slice`).
There are zero sorries left in the item and zero holes added or split off.
No new theorem, definition, or axiom is introduced.

## No longer needed

No original dependency node or module is pruned: the finite normalization,
ordinary operations, and canonical slice construction are all used. No public
imports were removed. No new intermediate theory is needed. The already proved
private `chartDerivedEquivalence` helper is used without the specialized perfect
complex theorem in its module; the node now records that module dependency and
explicitly identifies the unrestricted helper used. The scalar/slice comparison
is `Iso.refl`, so no separate import of
`Sheaf.Paper.IntegralPullbackScalarComparison` is required.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct. Its original proof dependencies omitted the
existing general chart-derived equivalence in
`Sheaf.Paper.PerfectChartTensorComparison` and the exact derived slice API in
`Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`. Both are now recorded.
Mathlib searches found generic module slice APIs, but the existing project helpers
already provide the needed pro-etale and coefficient comparisons.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
