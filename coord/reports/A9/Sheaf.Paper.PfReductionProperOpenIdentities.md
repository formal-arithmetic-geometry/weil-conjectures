## What changed

Replaced the single proof hole in `Sheaf.Paper.PfReductionProperOpenIdentities`
by the naturality field of the proper mate, two scalar-unit pasting calculations,
and proper/open tensor mate calculations. The given target statement and all
existing public definitions remain identical. All added proof helpers are private
and proved; proof-only imports keep their dependencies out of the public interface.

The scalar-unit calculation is proved abstractly from a scalar counit square by
adjunction injectivity, counit naturality, and the triangle identity. Existing
`ProperScalarCounitSquare` and `OpenScalarCounitSquare` give its two geometric
specializations, transported through the normalized scalar and open models.

Two separate coherence results have their own source-backed modules and nodes:
scalar/pullback tensor compatibility and scalar/pullback geometric composition.
The main proof combines these with the existing fully proved abstract mate
calculations in `RingedExchangeTensorCoherence` and
`OpenScalarTensorNormalization`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.PfReductionFactors.pfReductionProperOpenIdentities`
(node `lem-sf-pf-reduction-proper-open-identities`), with zero holes remaining in
its module. The five conjuncts are combined by a complete Lean proof.

Added one remaining hole:
`AlgebraicGeometry.ProEtale.OpenScalarTensor.scalarPullbackTensorCoherence`
(node `lem-sf-scalar-pullback-tensor-coherence`). Its proof is exactly `by sorry`;
its source and full representative proof are in its docstring and node. This is
a decomposition of the original hole, not a net decrease of the hole count.

`AlgebraicGeometry.ProEtale.OpenScalarTensor.scalarPullbackCompositionCoherence`
(node `lem-sf-scalar-pullback-composition-coherence`) is proved from the existing
ordinary composition, localization, and adjunction mate declarations; it adds
no hole. Every new private helper is proved. Existing dependencies may still
contain their own recorded holes; no final axiom-free claim is made here.

## No longer needed

Removed the direct proof imports:

- `Sheaf.Paper.ProEtaleScalarMateNormalization`: naturality is the mate's own field.
- `Sheaf.Paper.CompactSupportIntrinsicTensorComparison`: no compact tensor model
  comparison is needed for the scalar-unit calculation.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: the already supplied
  scalar adjunctions and their normalized coordinate isomorphisms suffice.
- `Sheaf.SixFunctors.OpenTensorNormalization`: the supplied inverse-adjunct fields fix
  the projection presentations directly.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`: geometric composition is used
  through the new, proved composition module instead.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`: its equal-universe system
  does not supply the needed equation for arbitrary pro-etale models.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`: its operations are
  available through the statement imports and counit-square dependencies.
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`: no separate
  direct-image/restriction identification is needed beyond the existing definitions.

Removed old direct proof dependencies: `def-coef-compact-support-tensor-comparison`,
`lem-fix-proetale-scalar-mate-normalization`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-sf-compact-support-restriction-of-scalars`, `lem-sf-open-tensor-normalization`,
`lem-sfb-kflat-scalar-comparison-normalization`, `lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-pbc-ring-sheaf-change-adjunction`,
`lem-weil-proetale-direct-image-restriction-of-scalars`.
Only the open tensor normalization and ringed exchange coherence remain in the
old top-level `tool_uses` list. These removals concern direct steps only. The old
compact-support-restriction theorem and
`def-coef-compact-support-tensor-comparison` are also no longer direct proof steps:
the independently defined scalar coordinates and intrinsic restriction are used.
Some removed direct imports remain transitive dependencies; no claim of their
withdrawal or of pruning their entire target closure is made. No source-library
declaration is removed, no module is withdrawn, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The planned specialization of the existing ringed tensor-square presentation does
not directly typecheck on the pro-etale sites used here: that presentation identifies
the site object and Hom universes, whereas these sites have object universe u+1
and Hom universe u. Its abstract mate calculation is universe-polymorphic and
can be used directly. The missing normalization equation is stated separately
for the actual canonical pro-etale pullback and arbitrary normalized models.

`open_scalar_tensor_models` supplies the tensor compatibility for an existential
choice of models and tensorators. The assigned theorem quantifies over arbitrary
normalized models and choices, so that existential result cannot supply the needed
hypothesis. The new tensor coherence statement retains this quantification.

The scalar-unit steps can be obtained directly from the existing proper/open
scalar counit squares. This avoids redoing the representative calculation for
these two steps.

## New nodes

`lem-sf-scalar-pullback-tensor-coherence` records only the four-left-adjoint tensor
coherence equation, without any proper projection, open extension, or compact-support
map. It is strictly a part of the proper and open arguments and is shared by both.
Its docstring and node give the flat-term K-flat representative proof, including
sheafified pure generators, signed totalization, and descent to arbitrary inputs.

`lem-sf-scalar-pullback-composition-coherence` records geometric composition of
inverse lambda with the canonical pullback compositors. It is the separate
composition result used after the normalized open tensor square. Its source and
proof use section-normalized ordinary composition, exact localization, and
composition of adjunction mates. The lemma is fully proved in this delivery.

No definition/statement change record is needed: no existing signature, definition,
visibility, or public import is changed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
