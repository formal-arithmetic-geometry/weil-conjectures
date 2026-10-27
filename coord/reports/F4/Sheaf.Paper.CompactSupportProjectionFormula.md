## What changed

Decomposed `WeilConjectures.compactSupportProjectionFormula` into its finite,
integral and field coefficient-stage obligations. Its proof now unpacks these
three conjunctions and assembles the original conjunction, including all finite
levels and all finite coefficient fields. The original signature is unchanged.
The three stage modules are private proof imports; their statements publicly
import only `Sheaf.Paper.ConstructibleProjectionMates`. They do not import the
item module, so there is no circular use of the original projection theorem.

Preserved all existing declarations, signatures, public imports and completed
proofs. Replaced the body of `CompactSupportPbcTransport.realization` by its
existing definitionally equal name `CompactSupportCoefficientTensor.rational`;
see `coord/changes/compact-support-projection-realization-alias.md`. Added local irreducibility attributes for the constituent mate and
adjunction definitions before `CompactSupportWeilProjection.component`, and
kept transparency respected while elaborating that definition. This avoids
expanding large concrete category expressions; its term is unchanged. No consumer adaptation is required. The existing unique-choice definitions
are preserved verbatim; a direct-choice performance experiment was reverted
because profiling showed it was slower.

Factored `tensorComparisonArrow` through the new fully defined generic
`projectionTensorArrowAssembly`. Unfolding it yields the original composite.
Its module is a public import because the public definition uses its body.
See `coord/changes/compact-support-projection-tensor-assembly.md`.

Validation: the three stage modules and generic assembly module compiled with
`lcompile.py --all`; after the final profiling-guided refactor the main item
compiled cleanly in 53.7 seconds. No profiler settings or scratch modules remain.

Updated the parent node's proof route and added a node for each stage obligation.
The finite/reduction/adic/field/coherence route of the blueprint unit is retained.

## Proved and sorry left

This is a decomposition, not a completed proof of the projection formula. One
upper hole is closed by assembly, and three strictly smaller stage holes are
added: seven original holes become nine holes across this packet. No net hole
reduction is claimed. Each new statement contains only the indicated coefficient
part, rather than the whole original theorem under another name.

Closed by decomposition:
- `WeilConjectures.compactSupportProjectionFormula`
  (`fix-prop-projection-formula`).

The six unchanged holes in the item module, all attached to
`fix-prop-projection-formula`, are:
- `WeilConjectures.compactSupportProjectionFormula_coefficients`.
- `WeilConjectures.CompactSupportWeilProjection.openMate_isIso`.
- `WeilConjectures.CompactSupportWeilProjection.restriction`.
- `WeilConjectures.CompactSupportPbcTransport.bridge_existsUnique`.
- `WeilConjectures.CompactSupportPbcProjection.forward`.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification`.

Added holes:
- `WeilConjectures.compactSupportProjectionFormula_finiteStages`
  (`lem-sf-projection-finite-stage-laws`).
- `WeilConjectures.compactSupportProjectionFormula_integralStages`
  (`lem-sf-projection-integral-stage-laws`).
- `WeilConjectures.compactSupportProjectionFormula_fieldStages`
  (`lem-sf-projection-field-stage-laws`).

The finite statement keeps arbitrary bounded constructible first inputs and the
finite-Tor second-input category. The integral statement keeps exactly the
original uniform finite-Tor predicate. The field statement keeps the entire
second-input domain. The splitting introduces no new hypothesis. Edge cases
checked against the original statements and constructions: zero inputs, identity
compactifications and field inclusions, the first finite level, and level index
zero in the recorded normalization (no new positivity assumption was added).
The coherence and proper-counit clauses are included in every stage's Laws.

## No longer needed

None. No original import, declaration, dependency node or module is withdrawn.
The concrete mate dependencies are retained in the parent because its other six
unfinished statements still need their argument. The three new obligations
reuse those dependencies in their proof plans. Mathlib searches for these
coefficient-stage laws found no matching theorem; the similarly named package
realization statements already use this item and cannot supply a shorter route.

## Where the brief, the DAG or earlier work was wrong

The pre-existing `STATEMENT-DISPUTED` comment at `bridge_existsUnique` reports
a missing completion-tower comparison in its HEq normalization. That separate
statement is preserved and remains a hole; this packet does not claim to settle
that dispute. No mathematical correction is asserted. The existing module's unrestricted
transparency setting at `component` caused expensive unfolding of the concrete
mate/adjunction definitions during server compilation. Local irreducibility
preserves its actual expression while controlling that unfolding. A direct
proof attempt for `forward` was not completed and is not included in this
packet; its original statement and hole are preserved.

## New nodes

`lem-sf-projection-finite-stage-laws`, in
`Sheaf.Paper.CompactSupportProjectionFiniteStages`, isolates the finite formula,
etale/pro-etale comparison and finite mate coherence, uniformly over all
finite levels and finite coefficient fields.

`lem-sf-projection-integral-stage-laws`, in
`Sheaf.Paper.CompactSupportProjectionIntegralStages`, isolates the integral cone
and Nakayama argument and realization of coherent system equalities. Its plan
uses the finite-stage obligation.

`lem-sf-projection-field-stage-laws`, in
`Sheaf.Paper.CompactSupportProjectionFieldStages`, isolates rationalization and
common-field descent of maps, inverses and coherence. Its plan uses the
integral-stage obligation. Each new module has one named theorem with its source
and proof in words and a matching DAG node. Change records:
`coord/changes/compact-support-projection-realization-alias.md`. No statement changed.

`def-sf-projection-tensor-arrow-assembly`, in
`Sheaf.Paper.ProjectionTensorArrowAssembly`, is a real generic composition of the
three specified arrows. It has no hole and introduces no additional proof
assumption. The tensor-assembly change record is
`coord/changes/compact-support-projection-tensor-assembly.md`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
