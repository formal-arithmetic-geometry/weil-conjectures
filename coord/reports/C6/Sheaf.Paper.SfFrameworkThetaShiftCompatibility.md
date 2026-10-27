## What changed

The original declarations and all public imports of
`Sheaf.Paper.SfFrameworkThetaShiftCompatibility` are unchanged. Its theorem now
pastes shift-compatible realization and whole-system counit transformations,
cancels the common target comparison, transports through the full constructible
inclusion, obtains the inverse equation, and applies raw rationalization.

Four new modules isolate the argument. `IntegralComparisonCanonicalShifts`
constructs total-limit and exact pullback shifts, the adjoint reduction shift,
and the universal-counit-normalized system scalar shift.
`IntegralComparisonSequenceScalarPullbackShifts` proves compatibility of the
specified strict-system scalar/pullback comparison by K-flat computation and
naturality. `IntegralComparisonPullbackRealizationShifts` and
`IntegralComparisonScalarRealizationShifts` state the two independent unary
realization calculations. The latter are used twice each, for the relevant
fields and schemes. They concern single operations on the ambient derived
category; neither states theta compatibility or repackages its hypotheses.

The main proof includes a generic private counit-pasting lemma. It inserts
the associators and the right unitor before identifying the component formula;
definitional equality of the underlying functors alone does not identify their
composite shift structures.

The reduction uses the original unit route and does not change a target,
existing definition, existing theorem signature, or adopted-source declaration.

## Proved and sorry left

Closed in the item: `WeilConjectures.sfFrameworkThetaShiftCompatibility` (one
original hole). This is a decomposition, not a net reduction in holes.

New proved statements:
`WeilConjectures.integralComparisonSequenceScalarShift_exists` and
`WeilConjectures.integralComparisonSystemScalarPullback_commShift`.
The canonical shift definitions contain no holes. Scalar shift data are chosen
from a proved universal-counit statement; no data depend on a new unproved
existence theorem.

Two added holes remain, each with its complete representative calculation in
its docstring and node:

- `WeilConjectures.integralComparisonPullbackRealization_commShift`, node
  `lem-sf-integral-pullback-realization-shifts`.
- `WeilConjectures.integralComparisonScalarRealization_commShift`, node
  `lem-sf-integral-scalar-realization-shifts`.

There are no holes in the item module. The delivery closes one hole and adds
two, so its local net is minus one. The two open calculations identify the
adjoint reduction shift on simultaneous quotient presentations and the
K-injective-normalized total-limit/Roos bridge with the prescribed signed
representative shift. They are strictly parts of the original proof, before
forming either lambda or mu; their conclusions are independently reusable.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Paper.CompletedScalarShiftDescent`,
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`,
`Sheaf.Algebra.Homology.RoosCommShift`,
`Sheaf.CategoryTheory.InjectiveTowerRoosShifts`,
`Sheaf.Paper.RingedCoefficientScalarShifts`,
`Sheaf.Paper.RingedCoefficientAssociatorShifts`,
`Sheaf.Paper.RingedCoefficientPullbackShifts`, and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.

These are replaced by the unary realization API and the proved strict-system
comparison. They are not claimed as globally pruned modules: K-flat resolution,
scalar descent, Roos comparisons, and coefficient computation remain below the
new statements or in existing public dependencies. No module is withdrawn.
The parent node drops the direct tool uses
`lem-pc-kflat-resolution`, `lem-weil-completed-scalar-shift-descent`,
`lem-pur-cochain-pullback-tensor-coherence`, `lem-weil-roos-comm-shift`,
`lem-pur-injective-tower-roos-shifts`, `lem-pur-coefficient-scalar-shifts`,
`lem-pur-coefficient-associator-shifts`, `lem-pur-coefficient-pullback-shifts`,
and `lem-pur-derived-change-of-rings`. The new node proof dependencies retain
the representative tools they actually need.

The main proof no longer directly invokes the coefficient-associator or
coefficient-pullback shift theorems; its counit squares follow from the fixed
adjoint shift, and its strict-system associator square follows directly from
universal scalar counits and exact termwise pullback. No source-library
declaration is removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The current blueprint Weil-structures paragraph motivates compatibility but
does not state the two unary realization results separately. Their complete
proofs in words are agent expansions of the original parent node steps 2–7
and of the cited Stacks comparison calculations.

The original numbered plan contains the mathematics of the representative
normalization calculation, but its supplied declarations do not state shift
compatibility of either ambient realization isomorphism. The supplied
coefficient shift theorems address their own coefficient-change models. They
do not directly instantiate the simultaneous reduction presentations and
Roos bridges in `IntegralComparisonRealizationModels`. The two new unary
statements make precisely this interface gap explicit. The remaining pasting,
cancellation, inverse, and rationalization steps are implemented in Lean.

Edge cases checked in the statements and argument: zero and negative shifts,
identity coefficient maps, identity scheme maps, and empty schemes. No
boundedness, finite-type, constructibility, or invertibility hypothesis is
added to the unary calculations. No assertion of faithfulness of separate
finite evaluations is used in the main proof.

## New nodes

`def-sf-integral-comparison-canonical-shifts` records the independently fixed
system shifts and the proved universal-counit construction. Its module is
`Sheaf.Paper.IntegralComparisonCanonicalShifts`.

`lem-sf-integral-pullback-realization-shifts` records the unary pullback
realization square, normalized by its unit-tensor generators and signed Roos
coordinates. Its module is `Sheaf.Paper.IntegralComparisonPullbackRealizationShifts`.

`lem-sf-integral-scalar-realization-shifts` records the unary scalar realization
square, normalized by its scalar generators, universal counit and signed Roos
coordinates. Its module is `Sheaf.Paper.IntegralComparisonScalarRealizationShifts`.

`lem-sf-integral-sequence-scalar-pullback-shifts` records the strict-system
comparison square proved by universal cochain computation and K-flat density.
Its module is `Sheaf.Paper.IntegralComparisonSequenceScalarPullbackShifts`.

Validation uses the prescribed remote compiler in dependency order. The
strict-system comparison and the generic cancellation lemma compile without
holes. The complete item module compiles cleanly in 41.5 seconds. The final
delivery command supplies its own compilation and axiom checks.

No change record is required: existing statements and definitions are unchanged.
The new modules have no existing consumers outside this delivery.

Generic tools requested for the new realization nodes are K-flat resolution,
cochain pullback/tensor coherence, signed Roos comparison and derived coefficient
change, inherited from the original plan. They supply representative and
localization calculations; they do not replace a unit statement or proof step.
The strict-system node uses K-flat resolution and universal coefficient change
for the same reason.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
