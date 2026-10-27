## What changed

Replaced the hole in `WeilConjectures.verdier_coefficient_realization` by a complete
assembly proof. The finite pro-etale clause is the second conjunct of
`finite_stage_verdier_biduality`; the boundary clause is `boundary_duality_input`.
The rational and common-stage clauses come from `coef_rational_verdier` and
`coef_qbar_verdier`, and the final exchange is `VerdierExchange.verdier_exchange`.

For the joint integral/rational clause, specialize `coef_rational_operations` to
the identity of T and the identity extension E -> E. Retain its structure system,
its integral dualizing datum, its rational datum, its HomIdentification and its
DualizingIdentification together. The integral conclusion is then
`integral_verdier_biduality` on exactly that datum. Construct the coefficient point
object explicitly as the completed regular module in degree zero. Its membership
comes from `integralConstantCoefficient_constructible` and `integral_residue_tor`;
its ambient unit comparison is the identity. No definition chooses arbitrary data
from an unproved existence assertion.

The only additional premise needed by the assembly is isolated in the new module
`Sheaf.Paper.IntegralDualizingExceptionalUnit`: a coherent integral dualizing datum
is isomorphic to the exceptional image of the coefficient unit. Its statement is
only an object comparison, uniformly in the normalized system and the coherent
presentation. It does not restate the four-stage duality or exchange theorem.
The node and docstring give the argument by coherent reductions and Roos triangles.
The original public signatures, definition bodies and public imports are preserved.
No source-library file or consumer is changed. The parent DAG proof now follows
this assembly and names its actual dependencies.

## Proved and sorry left

Closed the original proof body of `WeilConjectures.verdier_coefficient_realization`
(node `lem-sf-package-verdier-coefficient-realization`); no `sorry` remains in the
item module. Its assembly is proved from the published dependency declarations
and the new object-comparison lemma.

Added one hole, the entire proof of the public theorem
`WeilConjectures.integral_dualizing_exceptional_unit`
(node `lem-sf-integral-dualizing-exceptional-unit`). This is the only `sorry` in
the delivery. Thus one upper hole is decomposed into one strictly smaller hole:
one hole closed, one added, net zero. This is a decomposition, not a claim that
Verdier duality is now free of dependency sorries. Existing dependency holes are
unchanged. The initial assembly with only the exceptional-value step open compiled
through lcompile.py in 12.7 seconds. The final two-module lcompile.py --all run passed (exit code 0), including the
new module and the item with no unfinished proof steps. Delivery preflight is run
through the prescribed deliver3.py tool.

## No longer needed

Removed the private proof imports `Sheaf.SixFunctors.IntegralDualizing`,
`Sheaf.Paper.DualityPairing`, and `Sheaf.Paper.FiniteTorAmplitudeSites` from the
item. The predicates themselves remain available through the unchanged public
imports needed by the existing definition.

The parent proof no longer directly uses `prop-coef-integral-dualizing`: the
coherent datum is already supplied by `coef_rational_operations`. Its source
argument for the exceptional-unit identification is made precise in the new
object-comparison lemma. The parent also needs no separate invocation of
`lem-weil-duality-pairing`, whose specified evaluation transpose is already part
of `FiniteProEtaleVerdierBiduality`. No separate domain-conversion step using
`def-weil-finite-tor-amplitude` is required to apply `verdier_exchange`, because
its Assertion has exactly the required domains. The direct proof citations
`def-weil-boundary-duality-input` and `def-sf-verdier-exchange-data` are also
unnecessary: the matching theorems already return those exact predicates.
Their statement-dependency entries are retained where the statement uses them.
No module is withdrawn; none of these dependencies is asserted globally unused.

## Where the brief, the DAG or earlier work was wrong

The seven-step plan is mathematically consistent, but the recorded integral
proposition does not directly return the ambient isomorphism to an arbitrary
chosen System's exceptional value at the unit. Its Lean statement gives a
completed tower, reductions and a representing-property conclusion. The remaining
comparison requires combining coherent finite exceptional comparisons with
reconstruction; that is the new strictly smaller lemma. An arbitrary choice of
integral datum followed by independently chosen rational witnesses would not
supply the required same-witness conjunction, so the proof retains the witnesses
from one application of the rational-operations theorem.

Edge cases of the new statement: the empty scheme has zero objects on both sides;
at the coefficient point this is the regular module under the identity adjunction;
changing E or ramifying its uniformizer does not change the quotient-by-quotient
argument. Coherence is explicitly required by DualizingDatum. The conclusion is
Nonempty of an isomorphism and does not claim uniqueness of its arrow or that
reduction detects equality of maps. The unit route is preserved.

## New nodes

`lem-sf-integral-dualizing-exceptional-unit`, in
`dag/nodes/sec-six-functors/lem-sf-integral-dualizing-exceptional-unit.json`, states
only the exceptional-unit object comparison described above. Its new module is
`lean/Sheaf/Paper/IntegralDualizingExceptionalUnit.lean`. The full natural-language
proof uses the normalized exceptional coefficient mates, reduction of the regular
unit, coherence of w, and the two canonical completeness triangles. LeanFinder,
LeanSearch and Mathlib grep were run and recorded; none gave this comparison.
Blueprint searches for integral dualizing and dualizing exceptional found the
broader integral proposition but no separate declaration of this comparison.
No definition or statement repair and no change record is needed.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
