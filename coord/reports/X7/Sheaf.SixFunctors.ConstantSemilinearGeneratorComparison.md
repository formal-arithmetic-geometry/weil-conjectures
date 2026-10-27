## What changed

Proved five existing helper theorems in
`Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison`, preserving every existing
signature, definition and public import. Added private proof imports for the standard
finite-free quotient resolution, finite additive order, unrestricted normalized
reconstruction, intrinsic/legacy completeness comparison and infinitude of primes.
Updated the existing theorem node's proof plan and dependency list for these helpers.
No other Lean module is changed.

The coefficient proof reuses `standard_quotients_perfect` instead of rebuilding its
resolution. Exactness of ordinaryH is reflected through the forgetful functor to abelian
sheaves and transported through the fixed additive equivalence. Exactness of ordinaryU
is pointwise. The reduced-unit proof specializes the existing CBC theorem. The input
unit proof uses unrestricted reconstruction, with intrinsic completeness supplied by
Admissible. An auxiliary distinct prime only presents the existing completeness
predicate and adds no scheme hypothesis.

## Proved and sorry left

Closed 5 of the item's original 18 holes; added 0 holes and split off 0 statements.
All names below are in `WeilConjectures.GeneratorReduction`.

Proved:

- `constantCoefficientProperties`
- `constantReducedUnits`
- `ordinaryH_exact`
- `ordinaryU_exact`
- `admissibleUnit_isIso`

The following 13 existing holes remain, all attached to
`lem-sf-constant-semilinear-generator-comparison` and retaining their existing
source and natural-language proof docstrings:

- `ordinaryRho_existsUnique`
- `rho_existsUnique`
- `constantDirectUnderlying_existsUnique`
- `ordinarySystemDirectIso_existsUnique`
- `ordinaryIntegralDirectIso_existsUnique`
- `systemDirectScalarIso_existsUnique`
- `ordinarySystemPullMap_isIso`
- `integralDirectScalarIso_existsUnique`
- `constantOpenAdjunction_nonempty`
- `systemOpenScalarMap_isIso`
- `ordinaryIntegralPullMap_isIso`
- `integralOpenScalarMap_isIso`
- `constantSemilinearGeneratorComparison`

This is a partial delivery of proved helpers, not a proof of the main generator
comparison and not a decomposition into new obligations. In particular, the existing
normalization, scalar-comparison and proper/open square obligations remain open.

## No longer needed

None. All four original public imports support existing statements or definitions.
The unchanged main proof plan still needs its existing dependencies; this delivery
claims no node, module, generator route or unit step can be withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. Existing Mathlib postcomposition instances are available for
each diagram shape rather than directly as finite-preservation instances; the proof
of ordinaryU_exact therefore introduces a finite indexing category explicitly.
The existing unrestricted reconstruction theorem already supplies the input-unit
invertibility, so that helper needs no new effectivity lemma or scheme hypothesis.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
