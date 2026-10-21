## What changed

Proved `AlgebraicGeometry.Scheme.integralConstantRealization_exact_derived` in
`Sheaf.Paper.CompletedRealizationDerivedCohomology`. Reuse the common interface's
`integralConstantModule_exact` and `integralConstantModule_additive`, then unfold only
`integralConstantDerived` and `integralRealizationFactors` to apply Mathlib's triangulated
and shift-compatible factorization instances. All declaration signatures, definitions,
normalizations and public imports are unchanged. The DAG now records reuse of the
existing exactness proof rather than duplicating its argument. The natural homology and
shifted-module isomorphisms remain the existing canonical constructions.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.integralConstantRealization_exact_derived`
(node `lem-weil-pbc-completed-realization-derived-cohomology`). Added 0 holes; 0 textual
`sorry` remain in the item. No split-off statements. Server single-file compilation
checks the proof; delivery preflight checks all declarations and their axioms.

## No longer needed

Removed these five unused private imports:

- `Sheaf.CategoryTheory.FiniteTypeConstantExact`
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Localization.Predicate`

The first two planned steps need no separate direct invocation of
`lem-weil-pbc-finite-type-constant-exact`, `def-weil-pbc-proetale-site`,
`def-sf-site-constant-module-functor`, `lem-weil-pbc-completed-constant-sheaf-reduction`,
`def-pur-sheaf-tensor-product`, or `def-weil-sheaf-of-modules-category`: their role is
already implemented by the common interface's exactness theorem. These six nodes are
removed from this node's proof dependencies; the original statement dependencies stay.
Scalar restriction remains relevant to the normalization of the homology comparison.
The Mathlib homology/localization infrastructure remains available through the retained
public imports. No module is withdrawn, and this report makes no claim that these
modules or nodes cease to be needed by other library declarations or the target closure.
The unit's realized statement and proof steps are untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG expanded the exactness argument that is already
proved in `IntegralStratifiedPerfectModels`; reusing it avoids duplicating that work.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
