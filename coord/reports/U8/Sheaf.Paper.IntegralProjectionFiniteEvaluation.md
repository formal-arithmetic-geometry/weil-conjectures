## What changed

Replaced the body hole of `IntegralProjectionReduction.integralProjectionFiniteEvaluation`
by an explicit construction and diagram calculation. Its statement and public imports
are unchanged. The proof uses private categorical naturality lemmas for tensor and
support evaluation, constructs the tensor comparison through the full finite inclusion,
and supplies the explicit evaluated source and target isomorphisms.

Added `IntegralProjectionEvaluationFactors`: the ambient transported finite tensor,
the type of natural system tensor evaluation, and explicit support, pullback, input,
source and target evaluation composites. Every object and map is constructed from
supplied comparisons. No definition chooses a witness from an unproved existence theorem.

Added `IntegralProjectionTensorEvaluation`: a natural lift of any ambient system tensor
evaluation through the full finite inclusion, and the proved equation computing its
components. Added three separate geometric comparison modules, described below.
Updated the item's DAG proof and added nodes matching all new modules.

Static validation confirms that the original theorem signature and public imports
are identical to the current shared source. All new node dependencies resolve,
all recorded Lean statements occur verbatim, and all Lean lines are at most
100 characters. The only body holes are the three named theorems listed below.
The full sandbox compile checked all five supporting modules without errors.
The final item compiled in 29.0 seconds; its sole style warning requested a reason
for the local heartbeat setting, which is now supplied as a comment. Delivery runs
the final compile and preflight on the complete packet.

## Proved and sorry left

The original hole of
`WeilConjectures.IntegralProjectionReduction.integralProjectionFiniteEvaluation`
is replaced by a combining proof. The tensor lift and both generic naturality
calculations contain no holes. The additional proved public equations are
`liftedTensorEvaluation_hom`, `liftedTensorEvaluation_square`,
`partialTensor_map_left`, and `partialTensor_map_right`, all in
`WeilConjectures.IntegralProjectionReduction`. The private
`tensor_evaluation_square` and `support_evaluation_square` give the generic
naturality calculations.

Three holes are split off, one per new module:

- `WeilConjectures.IntegralProjectionReduction.integralProjectionSupportEvaluation`
  (`lem-sf-integral-projection-support-evaluation`): a unary support-adjunction
  evaluation identity, with no tensor, second input or projection map.
- `WeilConjectures.IntegralProjectionReduction.integralProjectionPullEvaluation`
  (`lem-sf-integral-projection-pull-evaluation`): a unary pullback-reduction
  evaluation identity, with no tensor, support or projection map.
- `WeilConjectures.IntegralProjectionReduction.integralProjectionSystemEvaluation`
  (`lem-sf-integral-projection-system-evaluation`): evaluation of the actual
  proper/open system projection in explicitly constructed endpoint coordinates.
  This contains no integral tensor, integral support adjunct, sourceMap, targetMap,
  TensorComparison or integral projection map.

This is a decomposition: one original hole closed and three holes added, for net
minus two. It is not an axiom-free proof of the projection formula. Each remaining
statement is strictly a separate part of the original argument; none restates the
original theorem under renamed or repackaged hypotheses.

## No longer needed

No existing import was removed and no module is withdrawn. Removed the unused
`IntegralProjectionCoordinateData` public import from the new evaluation-factors
module. The tensor, support and pullback comparison modules import it directly
because their public statements use its coordinates; the system-only module does
not need it. The original node's direct
uses of `lem-pur-normalized-integral-tensor-tower`, `lem-coef-integral-residue-tor`,
`def-fix-six-functor-datum`, `def-sf-integral-projection-coordinate-data`, and
`lem-sf-projection-scalar-square` are replaced by the explicit factor, tensor-lift,
support, pullback and system-evaluation nodes. The old inputs remain needed transitively
where their mathematics occurs. In particular finite-Tor membership is already proved
in `torReduction`, and the system projection node still uses the scalar-square
calculation. No claim of global pruning is made.

## Where the brief, the DAG or earlier work was wrong

The original plan combines the intrinsic finite tensor of the coefficient calculus
with the transported fixed-coefficient tensor used by the partial finite projection.
These are distinct presentations and are not definitionally equal. The new ambient
system evaluation comparison makes that bridge explicit; the full finite inclusion
then gives the natural integral tensor comparison without a new existential choice.

The support and pullback comparisons also require compatibility with the datum's
prescribed maps, not just existence of isomorphic endpoints. They are isolated as
unary equalities. The combining proof tensors these equalities, uses naturality of
support evaluation, and applies the system projection identity in precisely those
coordinates. The unit route remains the successive coefficient reduction argument
of `fix-prop-projection-formula.proof.md`; no target, existing definition, universe,
or geometric hypothesis was changed.

The new formulas cover m=0, zero inputs, identity opens and empty opens. They use
actual quotient scalar extension and never assume that quotient rings are flat over
the integral coefficient ring or that finite evaluations are faithful on arbitrary
morphisms of derived coefficient systems.

A read-only dependency check encountered an existing two-node cycle outside this
packet: `lem-pc-ring-hom-extension-differential` has a proof dependency on
`lem-pc-ring-hom-extension-differential-adjacent`, whose statement dependencies
include the former node. Both edges are present in the shared repository.
No node in that pair is changed here; this is reported for maintainer review.

## New nodes

`def-sf-integral-projection-evaluation-factors` records the explicit evaluation
composites and the ambient tensor comparison type. Its maps use the existing
supportEvaluation, pullbackTensorDerivedEvaluation and finite operation realizations.

`lem-sf-integral-projection-tensor-evaluation` records the constructed tensor lift
and its component equation, using the currying counit and full inclusion.
Its two map lemmas expose the restriction's action separately in each tensor input,
so elaboration can keep the large partial tensor definition abstract.

`lem-sf-integral-projection-support-evaluation` records the unary support identity.
Its proof plan expands the actual reconstruction adjunct and uses the chosen Roos
projection and datum supportProjection equation.

`lem-sf-integral-projection-pull-evaluation` records the unary pullback identity.
Its proof plan compares the same K-flat quotient model with the datum pullProjection
field and cancels its representative identifications.

`lem-sf-integral-projection-system-evaluation` records the projection identity on
systems alone. Its proof plan constructs the intrinsic/fixed tensor comparison on
K-flat models and pastes the proper counit, open tensor and pullback-compositor
squares. No integral-realization endpoint equation is hidden in this statement.

Searches with leanfinder, leansearch, loogle and grep, and direct project-source
searches, found the existing tensor, adjunction, evaluation and realization APIs,
but no theorem already expressing the three specialized comparison identities.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
