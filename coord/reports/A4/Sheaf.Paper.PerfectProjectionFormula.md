## What changed

Retained the earlier sandbox proofs and checked them against current sources.
Closed 15 original holes with no signature or definition changes. In particular,
constructed bounded quotient resolutions from the adic datum, proved quotient
site-perfectness and reduction invertibility, constructed the normalized quotient
pullback using the existing scalar-restriction comparison, and proved its tower
naturality from the constant-ring adjunct formulas. Coefficient composition coherence
proves the completed coefficient square. The earlier naturality, inverse-square,
flatness, K-injectivity and identity-compactification proofs are retained.

Added proof-only imports of Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree,
Sheaf.Paper.ProEtaleProjectionFormulaArrows,
Sheaf.Algebra.Homology.SplitPerfectTensorKInjective,
Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction,
WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom and
Mathlib.CategoryTheory.Preadditive.Biproducts. Moved the unchanged Resolution
structure and resolution_exists declaration before reductionMap_isIso so that its
proof can use the constructed resolution. The generic private moduleUnit_existsUnique
helper is fully proved and ordinaryUnit_existsUnique specializes it.

## Proved and sorry left

Closed 15 of the original 19 holes; added 0 holes, split off 0.
All names below are in AlgebraicGeometry.Scheme.PerfectProjection.

Proved: coefficientCone_naturality, coefficientMap_isIso,
quotientPullback_existsUnique, resolution_exists, reductionMap_isIso,
quotientModuleMap_existsUnique, quotientDerivedPullback_naturality,
tower_compatibility, operator_compatibility, mixed_existsUnique,
ordinaryUnit_existsUnique, Resolution.flat, Resolution.targetComplex_isKInjective,
coefficients_square, identityCompactification_compatibility.

Remaining 4 original holes, all attached to
lemma-weil-pbc-perfect-projection-formula: perfect_projection_formula,
ordinaryUnit_coherence, totalization_compatibility, baseChange_compatibility.

Every private helper is fully proved. These proofs use named library dependencies
whose proofs may still contain sorry; no claim of axiom closure is made.

## No longer needed

Removed proof-only import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations:
the proofs use the canonical ringed operations exposed by the statement imports.
No DAG dependency or unit route is pruned: the remaining obligations retain the
recorded localized perfect-complex and signed-totalization plan.

## Where the brief, the DAG or earlier work was wrong

The retained report understated the later proof work. Its unfinished resolution proof
needed an explicit finite-biproduct instance; it now compiles. The retained unsuccessful
ordinaryUnit_coherence simp proof remains the original named hole. No mathematical
statement mismatch or dispute was identified.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
