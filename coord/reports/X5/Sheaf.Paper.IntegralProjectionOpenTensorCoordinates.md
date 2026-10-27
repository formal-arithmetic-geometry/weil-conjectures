## What changed

Proved the assembly of integralProjectionOpenTensorCoordinates without changing its statement.
Constructed the natural open coefficient isomorphism from the existing ordinary open realization
and the inverse of the actual scalar mate. Its component formula, invertibility and naturality
are proved in IntegralOpenProjectionCoefficientData.

The argument first works in the actual operation functors, proves preservation of the inverse
projection by adjunction transposition, and cancels the two projection isomorphisms. It then
transports back to the stage coordinates of openMap, barTensorReduction, properPullReduction
and openReduction. The pullback-compositor equation is retained, including the compactification
factorization equality. The generic naturality and mate calculations are fully proved private
helpers, with the categorical calculations following CommonProjectionOpenFactor.
Local irreducibility of the large coefficient functors and componentwise equality transports
keep the calculations from unfolding the Roos and derived-category constructions. These local
proof settings change no shared interface.

Validation: lcompile.py --all compiled all five sandbox modules successfully after removal of
profiling output. The original declaration statement is unchanged, the new node statements match
the Lean declarations, and the revised dependency graph has no cycle.

## Proved and sorry left

Closed the original hole in
WeilConjectures.FixProjectionCompactification.integralProjectionOpenTensorCoordinates
(node lem-sf-integral-projection-open-tensor-coordinates).

Two normalization obligations remain as separate public theorems:

- WeilConjectures.IntegralProjectionReduction.OpenCoordinates.integralOpenAdjunctionReduction
  (node lem-sf-integral-open-adjunction-reduction): the unit and counit coefficient squares,
  involving no tensor or projection.
- WeilConjectures.IntegralProjectionReduction.OpenCoordinates.integralDatumPullCompositionReduction
  (node lem-sf-integral-datum-pull-composition-reduction): only the pullback-compositor
  coefficient square, involving no tensor, open extension, or projection.

This is a decomposition: one original hole closed, two holes added. The auxiliary
integralOpenPullTensorReduction is proved from the existing canonical completed tensor
reduction theorem integralComparison_reduction in DerivedPullbackTensorIso, using a private
import all, the public canonicalIntegralPullbackTensor_reduction component formula, the supplied
normalization equalities and inverse-square cancellation.
The auxiliary reduction_isIso and extensionComparison_hom_app are also proved.
No sorry is placed inside a definition or private helper.

## No longer needed

No existing module or declaration is withdrawn. The original two public imports are preserved
because the unchanged statement uses their definitions. The new tensor and compositor modules
import IntegralProperProjectionCoefficientData directly; their statements and proofs do not need
the new open coefficient construction.

The old direct proof dependencies def-sf-operation-stages, def-fix-six-functor-datum,
lem-sf-generator-reduction-coherence, lem-sf-open-reconstruction-effectivity and
lem-coef-integral-residue-tor remain needed below the new coefficient modules. None is globally
pruned. The generic generatorReductionCoherence theorem is no longer needed directly in the assembly:
the precise open-adjunction and pullback-compositor normalizations are now explicit obligations,
and the pullback/tensor square uses the existing canonical reduction theorem. Its node remains
a dependency of the two normalization obligations, so this is not a claim that its module is
pruned from the targets' closure. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan described the passage from generator word coordinates to the datum's normalized
operation comparisons in prose; no declaration supplied these identifications. The missing
identifications are now stated separately, with actual maps and endpoints, rather than another
projection square. The canonical pullback/tensor reduction square already exists in
DerivedPullbackTensorIso, so another unproved geometric tensor square is unnecessary.

Identity maps, zero inputs and empty opens require no additional hypotheses. The natural open
comparison uses the residue-Tor theorem and open reconstruction effectivity on each constructible
input. The tensor proof uses the base structure map to supply residue invertibility.
All remaining normalization proofs are statements about strict quotient maps and their actual
augmentations, and do not infer equality from faithfulness of finite derived evaluation.

## New nodes

- def-sf-integral-open-projection-coefficient-data: explicit natural open coefficient comparison,
  proved invertibility and the component formula; no arbitrary existence witness is selected.
- lem-sf-integral-open-adjunction-reduction: unit and counit comparison for open extension.
- lem-sf-integral-open-pull-tensor-reduction: inverse pullback/tensor comparison, proved from the
  existing canonical completed comparison.
- lem-sf-integral-datum-pull-composition-reduction: pullback composition comparison.

No existing interface is changed, so no change record or forced consumer adaptation is needed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
