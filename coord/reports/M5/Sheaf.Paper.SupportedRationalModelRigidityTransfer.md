## What changed

The original theorem `AlgebraicGeometry.ProEtale.CondensedRing.supported_rational_model_rigidity_transfer`
now has a complete combining proof. Its signature and public imports are unchanged.
The only private proof import is `Sheaf.Paper.SupportedRationalLatticeGeneration`.
The original node records the new proof route; the blueprint unit route is retained.

Two new modules isolate independent steps of the original argument.
`SupportedCoefficientLocalization` defines exact coefficient localization by a specified
regular-module ell-telescope and states transfer for one module.
`SupportedRationalLatticeGeneration` defines localized supported integral generators and
states finite extension-product generation of supported rational models. Both definitions
are complete; neither chooses data from an unproved existence theorem.

The combining proof applies hR on each integral support path, uses individual localization,
transports invertibility across the supplied derived isomorphism, and inducts over the
finite extension product. The existing proved `closed_restriction_derived_operations`
supplies the triangle morphism for the actual restriction, and Mathlib's
`isIso₂_of_isIso₁₃` supplies extension closure. No existing public interface or source-library
file is changed.

## Proved and sorry left

This is a decomposition, not a net proof gain: one original hole closed and two new
holes added. The item module has zero remaining holes. The complete combining proof is
`AlgebraicGeometry.ProEtale.CondensedRing.supported_rational_model_rigidity_transfer`.

The only remaining holes in the delivered files are:

- `AlgebraicGeometry.ProEtale.CondensedRing.supported_coefficient_localization`, node
  `lem-sfb-supported-coefficient-localization`, in its own new module.
- `AlgebraicGeometry.ProEtale.CondensedRing.supported_rational_lattice_generation`, node
  `lem-sfb-supported-rational-lattice-generation`, in its own new module.

Each has proof exactly `:= by sorry`, a source and complete proof in words in its docstring,
and a matching node. The first concerns one arbitrary module, with no support paths or
stratification. The second has no closed pair or cohomological hypothesis and concludes
only generation. Neither restates the original theorem under another name.

Edge cases checked: rank zero, empty path sources, varying finite ranks, identity root
paths, identity closed immersion, empty closed fibre, and independent coefficient-ring
isomorphisms. The telescope construction respects the zeroth coefficient-map leg, so it
specifies the actual ring action. No complement condition is imposed on the fixed pair.

## No longer needed

Removed private imports from the item module:

- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`
- `Sheaf.Paper.QcqsLisseStratifiedIntegralLattices`
- `Sheaf.Paper.QcqsConstructibleIntegralLatticeTree`
- `Sheaf.Paper.PadicIntegersInvertEll`
- `Sheaf.Paper.QcqsLatticeTreeReconstruction`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
- `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`

Removed direct proof dependencies (deferred to the split statements where applicable):

- `def-weil-closed-immersion`
- `def-weil-open-immersion`
- `lem-weil-pbc-vector-space-free`
- `lem-sfb-constant-finite-free-presentation-extension`
- `sk-def-sfb-constructible`
- `lem-sfb-qcqs-lisse-stratified-integral-lattices`
- `lem-sfb-qcqs-constructible-integral-lattice-tree`
- `det-prop-sfb-qlbar-colimit-x-invert-ell`
- `lem-sfb-qcqs-lattice-tree-reconstruction`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-proetale-closed-underived-projection`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-sfb-comap-preserves-k-injectives`
- `lem-coef-derived-sections-scalar-coherence`
- `lem-sfb-internal-module-operations-transport`
- `lem-sp-kinjective-comparison-principle`
- `sk-def-sfb-change-of-scalars`
- `det-pe-bounded-continuity-sections`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-sp-grothendieck-enough-injectives`
- `det-prop-sfb-module-pullback-exact-main`
- `lem-weil-pbc-injective-resolution-ses`
- `lem-weil-pbc-horseshoe-morphism-lift-exact-source`
- `lem-weil-pbc-complex-ses-triangle`

The geometric, coefficient and continuity inputs remain needed in the two split-off
arguments and are recorded in their nodes. They are not claimed as globally pruned.
The old explicit horseshoe construction (step 6) is unnecessary: the existing proved
actual-restriction triangle theorem supplies its result. The item no longer directly
uses the old Grothendieck/enough-injective, exact-pullback, horseshoe-resolution,
horseshoe-morphism-lift and short-exact-triangle nodes. Some remain transitive inputs
of other declarations; none is withdrawn.

All fourteen old top-level `tool_uses` approvals were removed from the item's node:
its direct proof now uses the two new statements, the existing derived-operations
statement and the triangle-isomorphism theorem. No approval was added or reordered.
Their applicable generic inputs remain in the new nodes' proof dependencies.
No module is withdrawn and no adopted source declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The seven-step argument is mathematically compatible with this reduction. Its existing
interfaces do not directly supply two pieces of glue: (a) coefficient forgetting must
identify the actual derived restriction, together with the tensor-telescope comparison;
(b) the standard coefficient inclusion must be transported along the arbitrary ring
isomorphisms, and stratified lattices must give appended paths and finite extension
products in the current tree interface. These are precisely the remaining statements.
The explicit horseshoe argument can be replaced by the already proved triangle API.

The torsion-rigidity hypothesis is retained verbatim and remains unused in this
conditional implication, as the old proof already noted. No target statement changes.

## New nodes

`lem-sfb-supported-coefficient-localization`, module
`Sheaf.Paper.SupportedCoefficientLocalization`, isolates original steps 4--5:
localization of an individual module through bounded-below continuity and coefficient
forgetting compatible with the actual restriction. Its predicate only specifies a
regular-module telescope, with no hollow data or arbitrary choice.

`lem-sfb-supported-rational-lattice-generation`, module
`Sheaf.Paper.SupportedRationalLatticeGeneration`, isolates original steps 1--3 and
the geometric part of step 7: stratified lattices, appended support paths, scalar
projection comparisons and finite distinguished-triangle reconstruction. It assumes
no comparison property and no global lattice.

No change record is needed because no existing statement or definition is changed.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
