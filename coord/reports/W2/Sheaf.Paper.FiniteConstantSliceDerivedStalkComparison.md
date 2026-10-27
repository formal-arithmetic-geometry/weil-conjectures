## What changed

Proved `AlgebraicGeometry.Scheme.finiteConstantSlice_derivedStalk_comparison`.
Its signature and its two public imports are unchanged. The delivery changes
only the assigned Lean module, its own DAG node, and this report.

Private helpers in `FiniteConstantSliceStalkProof` construct the equivalence from
modules on the actual ringed slice to fixed-scalar sheaves on the chart. They
identify representative-based derived slice restriction with exact derived
restriction and cancel the actual derived coefficient change along the given
isomorphism. These constructions adapt the proved scalar and slice arguments in
`FiniteCoefficientSliceModelTransport`; they require no finiteness of B. All
private definitions have actual data and every private theorem is fully proved.

The functor F is the derived slice equivalence, followed by the exact geometric
point fibre from `ProEtaleFiniteModelStalks`, followed by the inverse scalar
restriction from `ULift B` to B. The natural constant-fibre isomorphism identifies
all differentials of the constant complex. The unit of the scalar equivalence
cancels the two opposite scalar restrictions. F is constructed before P is
introduced, so the same F works for every complex.

Validation: the final assigned module compiled successfully in 31.4 s, with no
warnings, against the published build. Static checks confirm the original
statement and public imports are unchanged, all lines have at most 100
characters, and the updated DAG dependencies are acyclic. The temporary check
module has been removed; the delivery contains one Lean file.

## Proved and sorry left

Original holes: 1. Closed:
`AlgebraicGeometry.Scheme.finiteConstantSlice_derivedStalk_comparison`
(node `lem-weil-pbc-finite-constant-slice-derived-stalk-comparison`).

Added holes: 0. Remaining holes in the assigned module: 0. No new declarations
with sorry and no new modules are introduced. No shared definition is changed.

## No longer needed

No pre-existing import is removed and no module is withdrawn. The following
original direct proof dependencies are not needed for this proof:

- `def-sfb-site-derived-constant-module-functor` /
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`: the proof
  localizes the exact fibre and coordinate functors directly and uses
  `mapDerivedCategoryFactors` for their values on complexes.
- `lem-trf-proetale-pullback-stalk-coherence` /
  `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence`: point-fibre exactness
  suffices; no pullback-stalk coherence is needed.
- `lem-weil-proetale-constant-sheaf-stalk` /
  `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`: the natural fixed-module
  `Point.constantSheafCompSheafFiberIso` supplies the constant-complex comparison;
  a separate ring-valued constant germ calculation is unnecessary here.

These are removals from this node's planned direct dependencies, not claims that
these modules are unused throughout the library. Some remain indirect imports.
The slice-localization dependency is retained. No unit statement or proof step
is bypassed. The proof does not import `FiniteCoefficientSliceModelTransport`:
the necessary scalar/slice constructions are proved privately here. Its unrelated
marked-etale-origin transport, chart-transition comparison, and finite-ring
hypothesis are unnecessary. No existing declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The original plan did not identify the available
scalar/slice construction in `FiniteCoefficientSliceModelTransport`. Although
its public theorem assumes a finite ring, the construction of its coefficient
and constant-model comparisons works for an arbitrary commutative ring. The
present proof carries out precisely those constructions and the stalk assembly,
without another split of this obligation.

Edge cases: zero ring and zero complex are allowed, and no cohomological bound
is imposed. An empty chart cannot supply the given geometric point. The target
derived localization universe w remains the caller's chosen one. The geometric
point is an actual construction; no arbitrary witness is selected from an
unproved mere existence statement.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
