## What changed

Replaced the hole in `WeilConjectures.fieldShriek_lowerBound` by a complete combination
of finite-field exactness, finite-field and common-stage lower-bound proofs, and the
separate common-stage exactness lemma. Its signature is unchanged. The lower bound
uses exact open extension and orthogonality for its subsequent derived direct image.
The canonical realization transports this to integral objects. The recorded standard
classes then transport it to rational and common-stage objects. A truncation induction
turns cohomology vanishing into the standard lower bound, and the converse uses zero
truncations. Finite exactness uses the ambient fully faithful inclusion and raw scalar
localization. No definition or existing public signature changes. The change record
`coord/changes/F1-field-shriek-lower-bound-elaboration.md` documents the namespace
opens, universe names, transparency options and local irreducibility attribute
classified as interface commands by preflight. No consumer adaptation is needed.

Added `Sheaf.Paper.CommonStageCompactSupportExactness` for the genuine separate
common-stage exactness result in the source's opening scalar-extension paragraph.
Updated the item's proof route and dependencies in its node. The unit
`sk-l-dl-general-composition` has no realized nodes, so this shorter route does not
bypass any prescribed realized unit step.

## Proved and sorry left

Closed the original syntactic hole in `WeilConjectures.fieldShriek_lowerBound`
(node `lem-zl-field-shriek-lower-bound`). The item's module now has zero holes.
Added one hole in `WeilConjectures.sfCommonStageCompactSupport_exactness`
(node `lem-zl-field-shriek-lower-bound-common-stage-exactness`). Total packet: one
hole. This is a decomposition, not a net proof: one hole closed and one added.
The finite exactness and both lower-bound arguments are fully written Lean proofs.
The remaining lemma asserts only common-stage exactness; it contains none of the
cohomological lower-bound conclusion or finite-stage exactness conjunction.

Both delivered Lean modules compiled cleanly through the required remote compiler:
`CommonStageCompactSupportExactness` in 7.6 seconds and `FieldShriekLowerBound` in
6.1 seconds on this resumed session, exit 0, without warnings. The original dependent instance binder names
remain unchanged. No hole occurs inside a definition or a private helper.
The previous preflight axiom probe timed out after 60 seconds; preflight reported
that the merge reruns it. Ordinary compilation of both files completed successfully.

Further searches checked `ConstructibleExceptionalAdjunctionCoefficients`,
`CommonStageWeilShriek`, `ArbitraryFieldVerdier`,
`IntegralCompactSupportCoefficientComparison`, and
`RationalCompactSupportCoefficientCoherence`. None directly proves the remaining
statement: the first requires a finite-field datum and supplies its own action;
the next two concern different canonical functors; the last two use ambient or PBC
coefficient presentations. The outstanding work is the normalized beta comparison
and transport to the framework stage system, rather than the lower-bound argument.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompactSupportReductionTower`
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.FiniteCompactSupportConstructibility`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.FiniteStagePairCategory`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.LocalizedTStructure`
- `Sheaf.Paper.PbcCommonStageCones`
- `Sheaf.Paper.PbcDescentFunctors`
- `Sheaf.Paper.PbcQbarCategory`
- `Sheaf.Paper.PbcScalarExtension`
- `Sheaf.Paper.RationalCompactSupportCoefficientCoherence`
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.SfScalarExtensionComposition`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.Paper.IntrinsicQbarCategory`

The following former direct proof dependencies are absent from the new lower-bound
argument. Some remain transitively needed by realization or the split exactness lemma;
this list does not claim that all are unreachable from every target.

- `def-weil-constructible-standard-tstructure`
- `def-weil-derived-complete`
- `def-weil-pbc-common-stage-cones`
- `def-weil-pbc-finite-stage-pair-category`
- `def-weil-pbc-qbar-category`
- `def-weil-rationalization-karoubi`
- `det-pe-milnor-sequence`
- `det-sf-open-closed-extension-zero-limits`
- `lem-cbc-rational-compact-support-coefficient-coherence`
- `lem-fin-finite-type-fibre-dimension-bound`
- `lem-pur-completed-coefficient-pushforward-comparison`
- `lem-sc-fibre-dimension-after-base-change`
- `lem-sf-compact-support-restriction-of-scalars`
- `lem-sf-derived-truncation-triangle`
- `lem-sf-integral-compact-support-constructible`
- `lem-weil-compact-support-reduction-tower-functor`
- `lem-weil-finite-free-completed-scalar-comparison`
- `lem-weil-heart-short-exact-triangles`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `lem-weil-pbc-noetherian-submodule-finite`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-proetale-direct-image-restriction-of-scalars`
- `lem-weil-scalar-extension-composition`
- `prop-finite-compact-support-constructibility`
- `prop-weil-localized-tstructure`
- `prop-weil-pbc-descent-functors`
- `prop-weil-pbc-scalar-extension`

The torsion-kernel, pro-zero tower and Milnor argument is unnecessary for the lower
bound: the recorded integral realization already permits the direct right-adjoint
argument. Finite fibre-dimension bounds and geometric base-change dimension invariance
are likewise unnecessary for this lower-bound proof. The integral/rational heart
comparison and the heart-layer exact-sequence induction are replaced by the specified
standard-class representatives and the elementary truncation induction.

## Where the brief, the DAG or earlier work was wrong

The old nine-step plan is longer than needed for the lower bound. The existing
`sfQcqsCompactSupportRealization` permits the direct standard-t-structure proof.
The common-stage exactness step remains distinct: the action structure does not expose
`betaCommShift`, and an arbitrary natural isomorphism of exact functors cannot simply
be assumed to commute with shifts. The new lemma records this missing conversion
from the normalized tensor-unit scalar mates, rational localization and exact descent.
No false statement or changed mathematical definition is asserted.

## New nodes

`lem-zl-field-shriek-lower-bound-common-stage-exactness` realizes only the exact
common-stage functor part of the source scalar-extension/descent paragraph. Its module
is `Sheaf.Paper.CommonStageCompactSupportExactness`; its statement is independent of
cohomological lower bounds. The docstring gives the tower normalization and descent
argument, including why finite reductions alone are not used as a faithfulness claim.
The edge cases are zero objects, identity maps, empty schemes, repeated stages and
negative shifts; the categorical argument includes all of them. The change record is
`coord/changes/F1-field-shriek-lower-bound-elaboration.md`; it lists all 97
transitive consumers and their current holders. No existing definition or
declaration signature changed. The split statement is restricted to the finite-field
datum of the source and the item; it does not assert extra generality over arbitrary fields.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
