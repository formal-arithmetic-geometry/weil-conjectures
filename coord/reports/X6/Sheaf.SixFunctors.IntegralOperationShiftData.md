## What changed

IntegralOperationShiftData proves IndependentExpression.shift_naturality by a
real composition argument. The source uses the pointwise reduction shift's
naturality, the generic expression square, the pointwise component identity,
and total limit's fixed shift naturality. The integral conjunct applies the
generic expression square directly.

IndependentExpressionShiftNaturality contains the three generic shift data
declarations moved byte-verbatim from the item and a generic recursive naturality
step. IndependentExpressionReductionShift constructs the pointwise shift natural
isomorphism, proves replacement commutes with pointwise evaluation, and states
the component equation before the context shift and before total limit.
All data are explicit constructions; no object is chosen from mere existence.
A direct textual check confirms that the three moved declaration blocks are
byte-identical to the current shared source. The two new modules compiled in
52.0 and 52.6 seconds; final item validation is recorded below after compilation.

## Proved and sorry left

Closed the original hole
WeilConjectures.IntegralSystemRealization.IndependentExpression.shift_naturality.
This is a decomposition, not a net hole reduction: its complete Lean proof uses
four strictly smaller new steps. Of the original two holes, one is reduced and one
is untouched. Added three holes (a fourth, sourceShift_naturality, was closed by
the reviewer; see below):

- WeilConjectures.IntegralSystemRealization.IndependentExpression.sourceShiftComponent_decomposition
  (lem-pur-independent-expression-source-component-decomposition): the source
  component identity, before naturality in the input family.

- WeilConjectures.IntegralSystemRealization.IndependentExpression.sourceShift_naturality
  (lem-pur-independent-expression-source-naturality): PROVED by the reviewer
  (2026-10-26) from sourceShiftComponent_decomposition, naturality of
  pointwiseInputShiftIso, shift_naturality_generic and naturality of total
  limit's shift. As delivered it restated the first conjunct of the item.

- WeilConjectures.IntegralSystemRealization.IndependentExpression.shift_naturality_generic
  (lem-pur-independent-expression-shift-naturality): only recursive expression
  naturality, independent of reduction mates and total limit.
- WeilConjectures.IntegralSystemRealization.IndependentExpression.pointwiseShift_component
  (lem-pur-independent-expression-reduction-shift): only the pointwise reduction
  component identity, before the context shift and total limit.

The original remaining hole is
WeilConjectures.IntegralSystemRealization.limitShift_roos
(def-pur-integral-operation-shift-data), marked STATEMENT-DISPUTED.
The definitions pointwiseInputShiftIso and pointwiseContext_evaluate are fully
constructed/proved. The preexisting tensorShifts_existsUnique proof is retained.

## No longer needed

No original node, dependency or module is pruned. All four tensor uniqueness
imports remain necessary for the preexisting tensorShifts_existsUnique proof.
The independent occurrences, normalized tensor properties, field integral shifts,
Roos realization models, shifted-cone data and adjunction imports remain necessary
for the unchanged public definitions and statements. No import was added merely
to follow an unused DAG plan. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The current DAG proof describes only the four tensor uniqueness components;
it did not express the independent-input or pointwise-reduction glue. Its proof
now records those steps and the actual composition used by Lean.

STATEMENT-DISPUTED: limitShift_roos uses completedTensorShiftRoosIso, which shifts
the cone comparison by -1 and uses the unsigned shiftFunctorComm. For the stated
cone coefficients, this gives (-1)^r on the mapping-cocone's ordinary limit
coordinate. A normalized K-injective limit bridge sends the limit tuple to that
coordinate without a sign. For odd r the two sides therefore differ by a minus
sign on that tuple. The existing SignedCoconeShift.signedCoconeShiftIso explicitly
multiplies this same shifted-cone construction by r.negOnePow, and its proved inl
equation is unsigned, confirming the needed correction. This delivery flags the
problem without changing the Roos theorem or its dependent normalization data.
No certified counterexample is claimed.

Edge cases of the two new statements were checked before stating them: if the
input index type is empty there is no selected index, so both statements are
vacuous; a single variable reduces to the primitive shift naturality or selected
pointwise component. At shift zero neither argument needs normalization or
coherence of the primitive shift data: naturality alone suffices. At a tensor,
injectivity is essential to keep the selected label out of the other subtree. Repairing the common signed Roos interface
requires reviewing the completed tensor normalization consumers together.

## New nodes

lem-pur-independent-expression-shift-naturality records the recursive selected-slot
naturality argument and owns its new module's generic shift data. It is strictly
a part of the original conjunction: it contains neither reduction nor limit.

lem-pur-independent-expression-source-component-decomposition records the
source component composition from pointwise reduction, expression shift and total
limit; it contains no input-family naturality conclusion.

lem-pur-independent-expression-source-naturality records the source input-family
naturality square after applying the component decomposition and generic recursive
naturality.

lem-pur-independent-expression-reduction-shift records the pointwise reduction
component identity. It includes no naturality conclusion; it compares the existing
explicit component constructions at one object. The upper theorem combines it
with the source and integral naturality squares.

Change record: coord/changes/X6-independent-expression-shift-extraction.md.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
