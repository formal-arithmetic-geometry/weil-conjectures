## What changed

Completed the proof of
`AlgebraicGeometry.ProEtale.FiniteScalarCompletion.finite_scalar_local_model_complete`
without changing its signature. Refactored the quotient sequence through the actual
coefficient sequence and finite biproduct/single functors to avoid repeated normalization.
The changed definitions retain their actual quotient objects, scalar maps and transitions. The strict cone-to-quotient
comparison has the actual prescribed transition, augmentation and degreewise coordinate
formulas. The free completion unit is inverted using the limiting quotient cone and the
degreewise-epi Roos kernel comparison. Ordinary scalar presentations follow from the existing
two-term free resolution and a morphism of distinguished triangles. The existing strict
restriction comparison and covering conservativity give the local assertion. The global
condensed-point assertion uses the identity cover.

Added `Sheaf.Paper.IntegralCoefficientQuotientLimit`, with the actual positive quotient
sequence and cone, and a proved theorem that this cone is limiting and its transitions are
epimorphisms. The proof constructs the unique continuous integral-valued lift of compatible
finite-quotient functions, then transports the sectionwise limit through the canonical
continuous-ring realization. No object is selected from a bare existence assertion.

Updated the parent node proof, proof dependencies and proof origin to record these interfaces.
All five original blueprint proof stages are retained. Added proof helpers and imports; the new public finite biproduct functor and diagram-complex constructor support
the definition refactor. A locally registered, proved instance chooses degreewise
countable products directly. There are no adapted consumers or changed target statements.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.FiniteScalarCompletion.finite_scalar_local_model_complete`
(`lem-sfb-finite-scalar-local-model-complete`).

Also proved the new independent rank-one coefficient calculation:
`AlgebraicGeometry.ProEtale.AdicCompletion.integral_coefficient_quotient_limit`
(`lem-sfb-integral-coefficient-quotient-limit`).

Original holes: 1. Closed: 1. Added: 0. Remaining in both delivered modules: 0.
The sealed-definition version of the complete parent passed `lcompile.py` in 58.8 seconds;
the complete delivery is checked again against the current published build. The coefficient-limit module
also passes its single-file check. The theorem signature matches the original verbatim.
No unfinished statements are split off. Existing imported declarations are used as the stage-3
brief requires; this report does not claim to have closed their separate holes.

## No longer needed

Removed these direct proof imports:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Homology.FlatScalarCyclicResolution`
- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.ScalarModelFiniteFlatResolution`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`

The following original direct proof dependencies are replaced by the existing coefficient
short exact sequence, the new normalized quotient-limit calculation, the existing finite
constant-model resolution, and the existing strict restriction comparison:

- `det-prop-sfb-qlbar-colimit-x-integral-limit`
- `det-prop-integral-criterion-constant-coefficients`
- `lem-sfb-flat-scalar-cyclic-resolution`
- `lem-sfb-scalar-model-finite-flat-resolution`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-sfb-coefficient-sections-localization`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-proetale-countable-products-exact`
- `def-pur-localized-ringed-site`
- `lem-weil-proetale-surjective-tower-derived-limit`

The tower difference map uses the adopted source library’s repleteness theorem directly
(`det-pe-replete-epimorphism`), followed by its general one-minus-shift calculation.

Their obsolete parent `tool_uses` entries are removed, preserving the order of retained
approvals. This is pruning of the parent proof route and direct imports; no source declaration
or module is withdrawn. Some of these modules remain transitive dependencies of the retained
interfaces, and no claim of global library removal is made. The unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The original prose plan is mathematically valid. Several interfaces need normalization glue:
the representatives theorem uses the spectral-norm coefficient topology while the completion
interface uses the specified extension absolute value. Their induced topologies are equal;
the proof transports the entire local-model proposition along that equality. A generic
inverse-limit existence statement alone would not identify the scalar quotient projections,
so the new coefficient cone keeps those projections explicitly. The scalar action on a
single finite biproduct is identified by generic linearity and coordinate identities,
avoiding repeated unfolding of its monoidal construction.

Edge cases: the coefficient calculation uses no geometric condition on the scheme. Finite
biproducts and the single functor include rank zero. The scalar resolution applies to all
finitely presented modules, including zero and torsion. The covering conservativity argument
allows an infinite cover. No target, hypothesis or conclusion is weakened; the refactored definitions mean
the same actual finite powers and quotient maps.

## New nodes

`lem-sfb-integral-coefficient-quotient-limit` in
`dag/nodes/sec-six-functors-basics/lem-sfb-integral-coefficient-quotient-limit.json` records
the rank-one ordinary coefficient limit and transition epimorphisms, with a complete Lean proof
in `Sheaf.Paper.IntegralCoefficientQuotientLimit`. It is strictly part of the free case:
finite powers, the Roos kernel comparison, strict augmentation normalization, derived
completeness and covering descent are proved separately in the parent. Searches by leanfinder,
loogle and grep are recorded in the node; no matching internal-module cone theorem was found.
The definition refactor and consumer analysis are recorded in
`coord/changes/finite-scalar-quotient-sequence.md`. No existing public signature changes. The `freeComplex` body is unchanged; converting
its `abbrev` to `def` permits local irreducibility during proofs, reducing normalization.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
