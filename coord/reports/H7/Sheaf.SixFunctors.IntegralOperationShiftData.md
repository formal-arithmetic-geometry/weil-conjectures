## What changed

Proved `WeilConjectures.IntegralSystemRealization.IndependentExpression.sourceShiftComponent_decomposition`
from the existing `IndependentExpression.pointwiseShift_component`. After expanding
only the comparison definitions and composition formulas, map that component equation
through `coefficientSequenceLimit` and compose it with the context shift, endpoint
transport, and limit shift. Isomorphism extensionality finishes the proof.

Remote single-file compilation passed cleanly in 11.4 seconds.

The proof follows the existing node plan. No declaration signatures, definitions,
imports, attributes, or other modules changed. No new statements were introduced.

## Proved and sorry left

Closed 1 of the module's 2 existing holes:

- `WeilConjectures.IntegralSystemRealization.IndependentExpression.sourceShiftComponent_decomposition`
  (`lem-pur-independent-expression-source-component-decomposition`).

One existing hole remains:

- `WeilConjectures.IntegralSystemRealization.limitShift_roos`
  (`def-pur-integral-operation-shift-data`), still marked `STATEMENT-DISPUTED`.

Added 0 holes and split off 0 statements. This is a proof, not a decomposition.

## No longer needed

None. No imports or declared dependencies were removed; the existing pointwise
reduction component lemma supplies precisely the equation required by the plan.

## Where the brief, the DAG or earlier work was wrong

The previous H7 report said the dependent endpoint transports prevented using the
pointwise component lemma. Expanding the comparison definitions and mapping the
component equation through total limit resolves that mismatch without changing
any endpoint or statement. Reassociation applies the equation before the three
remaining factors.

The existing `limitShift_roos` dispute remains unresolved. Its unsigned shifted-cone
formula is already documented as missing the factor `(-1)^r` in the mapping-cocone
shift. This delivery preserves its statement and dispute marker and does not use
that theorem to prove the component decomposition.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
