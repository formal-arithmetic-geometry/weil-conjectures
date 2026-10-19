## What changed

Completed the proof of
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve`
with its complete original signature and visibility. No definition or statement changed.
The existing `isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`
(`cor-fin-deligne-open-finite-coefficients`) already gives the stronger result over any field.
Construct the invertible exponent from ell^n on nonempty T, descend it to k, place F in
degree zero, apply that theorem, and transport homology through
`Functor.rightDerivedFunctorPlusCompatibility`. Treat empty T directly by the empty-cover
axiom. The extra field and dimension hypotheses remain in the unchanged signature.

The theorem docstring and the existing node's proof, proof_deps and proof_origin now
record this route. The old tool_uses entries are withdrawn because none is used directly.
Added proof imports: OpenDirectImageFiniteCoefficients,
ConstructibleEtaleModuleSheafComparison, CategoryTheory.DerivedCategory.Constructible,
CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility, and
AlgebraicGeometry.InvertibleExponent (the last three under WeilConjectures).

The proof has no local holes or new declarations. The theorem's signature, visibility,
and public imports are identical to the current source. All Lean lines meet the
100-character limit. The linter option precedes the docstring, so that the docstring
attaches to the theorem and the unused retained field and dimension hypotheses do
not produce warnings. Final compilation and preflight results are recorded by the
delivery tool.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve`
(node `thm-exc-curve-open-constructible-general`).
Added 0 holes; split off 0 statements. No sorry remains in the item module.
The proof uses existing declarations; their entire dependency closure is not
claimed to be sorry-free. The existing broader open-image theorem ultimately uses the existing
generic Deligne constructibility hole; this delivery adds no such obligation.

## No longer needed

Removed proof imports (each unnecessary for the new proof):

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.FieldTheory.EtaleFieldGaloisClassification`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.ClosedPointField`
- `Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
- `Sheaf.RingTheory.StrictHenselizationDimension`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
- `WeilConjectures.AlgebraicGeometry.EtaleResidueTriples`
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `Sheaf.Paper.FiniteCoproductCohomologyAssembly`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward`
- `Sheaf.RingTheory.StrictHenselizationTriples`
- `Sheaf.RingTheory.StrictlyHenselianQuotient`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral`
- `Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
- `Sheaf.AlgebraicGeometry.Dimension`
- `Sheaf.AlgebraicGeometry.OpenDegreeZeroConstructible`
- `Sheaf.AlgebraicGeometry.OpenImmersionRestriction`
- `Sheaf.RepresentationTheory.DvrGalois`
- `Sheaf.RingTheory.FieldAlgebraStrictHenselizationExcellent`
- `Sheaf.RingTheory.PuncturedCurveBranches`
- `WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`

The following original proof dependencies are no longer used by this node. This is
pruning from this proof, not an assertion that other parents do not need them:

- `def-exc-continuous-cohomology`
- `def-kun-topological-krull-dimension`
- `def-weil-constructible-subset`
- `def-weil-finite-type-morphism`
- `lem-exc-affine-strict-local-ring-comparison`
- `lem-exc-dvr-galois`
- `lem-exc-etale-field-galois-classification`
- `lem-exc-field-algebra-strict-henselization-excellent`
- `lem-exc-field-discrete-modules`
- `lem-exc-punctured-curve-branches`
- `lem-kun-closed-point-field`
- `lem-kun-open-immersion-restriction`
- `lem-pc-scheme-dimension-local-rings`
- `lem-sbc-higher-direct-image-forget-comparison`
- `lem-sc-noetherian-closed-subset-finite-components`
- `lem-sc-scheme-sober`
- `lem-sc-strict-henselization-dimension`
- `lem-sfb-finite-field-separable-closure-algebraic`
- `lem-weil-pbc-affine-open-stalk-localization`
- `lem-weil-pbc-constructible-module-finite-stalks`
- `lem-weil-pbc-etale-module-cohomology-forget`
- `lem-weil-pbc-finite-coproduct-cohomology-assembly`
- `lem-weil-pbc-finite-separable-extension-etale`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-reduction-universal-homeomorphism`
- `lem-weil-pbc-strict-henselization-closed-fiber-backward`
- `lem-weil-pbc-strictly-henselian-quotient`
- `pqf-lem-locnoeth-lft`
- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-weil-pbc-strict-henselization-stalk-formula`
- `prop-weil-pbc-universal-homeomorphism-topos`
- `thm-exc-curve-open-dimension-general`
- `thm-fin-open-degree-zero`

All original `tool_uses` entries are stale and removed, including the two older stale
etale-local-ring-triples and strict-henselization-triples entries. The new proof uses none
of the boundary decomposition, local strict-henselization, punctured-branch or finite
Galois-cohomology calculations. Public statement-foundation imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically valid but longer than necessary given the current
library. The already delivered finite-coefficient open-image theorem supplies the result
without a curve hypothesis. Both its node and the source library were checked for a
dependency back to this item; none was found. The node is absent from every `realized`
entry of its unit, whose statement and proof steps remain untouched.

The new route uses `cor-fin-deligne-open-finite-coefficients` from another unit as an existing
stronger input. Please record any required maintainer tool approval; workers may not add
entries to `tool_uses`. Its exact finite-coefficient statement and its current Lean proof
were read. The constructibility-comparison node is also an existing proved generic tool.
The edge cases empty T, empty U, zero A, and negative q are covered: empty T is handled
directly; the broader theorem covers the others without a separate positive-degree argument.
No source or statement repair was needed.

The retained proof was checked against the current source on this resumption. The required
initial dry run passed compilation and preflight (dry-run commit `2ff5735cdb`, review class
CODEX because the proof route changes the node file). The retained parser repair places
`set_option` before the docstring, and all public imports match the source exactly.
The current transitive DAG check visits 400 nodes and finds no dependency from the
open-image theorem to this item. `tools/import_direction.py may` likewise confirms
there is no Lean import cycle. The broader theorem's current blueprint statement and
proof, its Lean implementation, the constructibility comparison, and the derived-functor
compatibility isomorphism were reread; the retained proof needs no further Lean changes.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
