## What changed

Replaced the original sorry in `coherent_frobenius_comparison` with a compiling proof
of exactly its original signature. It uses three strictly smaller mathematical steps:
the coherent power comparison (including scalar semilinearity), the structural
coherent-etale comparison square, and coherent Frobenius naturality for structural
pullback. These are the source node's Cech power, comparison and pullback steps.

The assembly is proved in Lean: invert the normalized power square through the fixed
module/abelian comparison; substitute hb in the structural comparison; then use
K-linearity, semilinearity on Y, hb, coherent Frobenius pullback naturality, and hb
backwards to prove the final tensor formula. The last step uses the supplied b and hb
and does not reconstruct a base-change isomorphism.

Only the item and three new theorem modules are delivered. Existing definitions and
all five Challenge target statements are unchanged. 44 obsolete direct
imports are removed; the exact list is below. Public import pruning is documented in
`coord/changes/Q4-coherent-frobenius-import-pruning.md`.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison`
(`lem-weil-pbc-coherent-frobenius-comparison`). The item now has zero sorries.

This is a decomposition, not a net proof: one old hole is closed and three lower
holes are added (net -2 before any closure pruning). The proved contribution is the
comparison inversion and the tensor formula assembled from the three named steps.
No claim is made that the remaining power and pullback steps are proved.

Every sorry left in the delivered sources, exactly one per new module:

- `AlgebraicGeometry.Scheme.Modules.coherentPowerComparison`
  (`new-coherent-power-comparison`): still needs the common Cech identification,
  its normalization, scalar action compatibility, and additive power naturality.
  It concerns one proper scheme and has no field extension, structural pullback,
  b, or tensor formula. Its scalar conclusion precedes the universally quantified
  etale map, so it can also supply semilinearity on Y without constructing FrE on Y.
- `AlgebraicGeometry.Scheme.Modules.coherentEtaleComparison_pullback`
  (`new-coherent-etale-comparison-pullback`): still needs the common-refinement edge
  square and fixed-resolution normalization identifying the specified etale and
  module pullback maps. It has no Frobenius or tensor conclusion and claims no
  flat base-change isomorphism.
- `AlgebraicGeometry.Scheme.Modules.coherentFrobenius_pullback`
  (`new-coherent-frobenius-pullback`): still needs the coefficient-transport square,
  structural ring-map power identity, Ext universe transport naturality, and
  cancellation through the fixed comparisons. It is intrinsic to any scheme
  morphism and has no fields, properness, etale comparison or tensor product.

All three statements have source citations and complete proof plans in their docstrings
and matching nodes. No definition or private declaration contains sorry. The existing
unique-normalized-comparison theorem remains an unchanged library dependency.

Edge checks: degree zero and empty schemes use the same section/edge identities.
Repeated affine intersections are allowed. The supplied maps are additive, so no extra
characteristic hypothesis is needed in the new lemmas. For p=0 this forces trivial
section rings; p=1 is the identity case. For structural pullback, refine a finite affine
cover of Y to inverse images of a finite affine cover of X; inverse images themselves
are not asserted affine. None of the new statements requires perfect fields.

Validation: `lcompile.py --all` compiled the structural comparison in 5.0 s, intrinsic
Frobenius pullback in 0.1 s, power comparison in 12.1 s, and the item in 24.3 s.
The item's signature was also compared with the shared original after whitespace
normalization and is identical. Every delivered Lean line has at most 100 characters.

## No longer needed

The supplied b and hb already provide the base-change isomorphism and its pullback
normalization. Reconstructing invertibility is redundant. This route does not need
`lem-pc-flat-cohomology-separated` / `Cohomology.FlatCohomologySeparated` or
`lem-weil-pbc-affine-triple-tensor-base-change` / `AffineTripleTensorBaseChange`.
The scalar action can be computed on resolutions and transferred through the fixed
comparison, so `lem-sc-cech-comparison-map-naturality` /
`CechComparisonMapNaturality` is also unnecessary. The corresponding two obsolete
main-node tool approvals are withdrawn.

The remaining Cech and site-change dependencies are retained in the new nodes; they
are not claimed as globally pruned. Original main-node proof dependencies absent from
the new direct and split proof plans are listed here; some still occur as statement
dependencies of the canonical constructions:

- `def-pc-base-change`
- `def-pc-module-pullback`
- `def-sc-etale-qcoherent-module`
- `def-sc-zariski-site`
- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-delta-functor`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-module-cohomology-fmap`
- `def-weil-pbc-site-cech-complex`
- `def-weil-pbc-topological-inverse-image`
- `def-weil-proper-morphism`
- `lem-pc-flat-cohomology-separated`
- `lem-sc-cech-comparison-map-naturality`
- `lem-weil-pbc-affine-triple-tensor-base-change`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-scheme-modules-enough-injectives`
- `new-module-cohomology-coefficient-factor`
- `pqf-def-coherent`

Removed direct imports from the item:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.Topology.Sheaves.Functors`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologySeparated`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology`
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`
- `Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`
- `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientFactor`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientTransport`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`
- `Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`
- `Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility`
- `Sheaf.CategoryTheory.RingedSiteCechRefinementSquare`
- `Sheaf.CategoryTheory.SiteCechComplex`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.CechComparisonMapNaturality`
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`
- `WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.Coherent`
- `WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`
- `WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives`
- `WeilConjectures.AlgebraicGeometry.Modules.Ext`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`
- `WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
- `WeilConjectures.CategoryTheory.DeltaFunctor`
- `WeilConjectures.CategoryTheory.SiteCechComplex`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`

## Where the brief, the DAG or earlier work was wrong

The plan reproves bijectivity of an isomorphism already supplied as b and normalized
by hb. The last tensor assertion only needs semilinearity and structural Frobenius
naturality. No false mathematical statement was found, and the unit's coherent
base-change/Frobenius step is preserved.

Work attempted the scalar and structural Ext calculations directly, with repeated
single-file compiles and diagnostics. Scalar action on a resolution was proved, but
the full fixed-comparison/Ext glue was not completed within the proving portion of
the budget. Those unclosed mathematical steps are recorded explicitly in the three
remaining statements; the delivery does not retain partially proved declarations.
Experimental changes to the canonical comparison implementation are not delivered.

## New nodes

`new-coherent-power-comparison`: the parent's Cech power step, with scalar
semilinearity and normalized additive power naturality, but no field extension.

`new-coherent-etale-comparison-pullback`: the parent's structural comparison step,
including the fixed-resolution normalization rather than an arbitrary equivalence.

`new-coherent-frobenius-pullback`: coefficient-transport and Ext naturality for the
structural power square. This is strictly a step of the tensor argument.

Each node records its source, exact Lean statement, full proof in words, Mathlib
searches, dependencies, and blueprint ancestry. Change record:
`coord/changes/Q4-coherent-frobenius-import-pruning.md`.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
