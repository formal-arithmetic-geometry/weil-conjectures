## What changed

Repair of returned delivery 2523e272ce8 (reviewer C-2523e). The landing failure
reported that the recorded signature of
`WeilConjectures.normalizedCommonEvaluation_naturality` differed from its source.
The current shared source has an independently landed module at
`Sheaf.Paper.NormalizedCommonEvaluationNaturality`, with that theorem name but a
canonical-structure signature. The returned packet used the same path and name
for a theorem about any normalized structure. This collision is now removed.

Moved our generic statement to the distinct new module
`Sheaf.Paper.NormalizedCommonEvaluationForStructure`, with theorem
`WeilConjectures.normalizedCommonEvaluationForStructure_naturality`. Its node keeps
the original id `lem-sf-normalized-common-evaluation-naturality`, updates its Lean
attachment and records the exact source signature. Updated the item's private
proof import and theorem application. The packet delivers no file at the
concurrent canonical module's path. All three delivered node signatures were
checked using the same declaration parser as the landing check.

The original common-field proof obligation remains in the renamed module. A
complete uniqueness-based wrapper using the concurrent canonical theorem compiled
on the server, but delivery refused its import because that dependency's landing
has not reached published `sheaf-dag`. That unpublishable dependency is removed;
the repaired packet uses the original rational evaluation dependency instead.

The main theorem `WeilConjectures.adicCommonStageHomTranspose` retains its entire
signature and every public import. Its proof transfers integral constructibility
through `sfDerivedComplete_iff_legacy`, uses
`integral_constructible_internalHom` for the finite-stage witness domain, and
obtains the normalized structure from `podCommonClosed_existsUnique`. Parameter
naturality and transpose injectivity prove the evaluation formula; the inverse
additive equivalence proves bijectivity. Tensor functoriality combines pair
naturality with the test-object arrow; braiding naturality followed by evaluation
gives the signed swap. The finite scalar clauses are exactly
`rationalHomScalar_transpose`.

The parent node's proof dependencies describe this assembly. No source-library
module, existing definition, statement or consumer changes. Delivery reconstructs
the packet against published `sheaf-dag`; the shared repository stays read-only.
The server compile and delivery preflight validate the final renamed packet.

## Proved and sorry left

The original hole in `WeilConjectures.adicCommonStageHomTranspose` is closed; the
item contains zero holes. Exactly two new holes remain:

- `WeilConjectures.normalizedCommonEvaluationForStructure_naturality`, node
  `lem-sf-normalized-common-evaluation-naturality`, in
  `Sheaf.Paper.NormalizedCommonEvaluationForStructure`.
- `WeilConjectures.commonTensorBraiding_naturality`, node
  `lem-sf-common-tensor-braiding-naturality`, in
  `Sheaf.Paper.CommonTensorBraidingNaturality`.

This remains a decomposition: one original hole closed and two split off, net
minus one before import-closure accounting. It is not a complete proof without
new holes. Evaluation pair naturality and tensor symmetry naturality are genuine
distinct parts of the argument. Neither states representability, bijectivity, the
witness-domain equivalence or finite scalar-transpose clauses. Existing imported
holes are unchanged. The repair itself adds no holes relative to returned head.

## No longer needed

The returned packet's generic module at the colliding path
`Sheaf.Paper.NormalizedCommonEvaluationNaturality` is no longer delivered. The
independently landed canonical module at that path is preserved. No existing
file is withdrawn and no deletion is requested. The renamed generic statement
retains the original rational naturality dependency, so the packet does not
require the unpublished canonical naturality landing.

As in the returned packet, removed direct private imports
`Sheaf.Paper.IntegralOperationsScalarComparisons` and
`Sheaf.Paper.CompletedTensorHomTranspose` from the item. Their direct node uses
`lem-pur-integral-operations-scalar-extension` and
`lem-coef-completed-tensor-hom-transpose`, including the two old top-level tool-use
approvals, are pruned. `def-weil-rationalization-karoubi` is no longer an explicit
proof dependency; its statement dependency and public imports remain. Existing
transitive dependencies may still use these modules, so no global module pruning
credit is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned packet failed to reconcile a concurrent module/declaration-name
collision before landing. The repair assigns a distinct generic module and
declaration name and synchronizes the recorded signature. It is a source and
node repair, not an unchanged re-push. The mathematical statement is unchanged.
The failed dependency experiment confirmed that server overlay compilation alone
does not mean an independently landed module is available to published delivery.

The original plan reconstructs data already provided by the normalized partial
closed interface. That interface's parameter naturality suffices for the evaluation
formula and bijectivity, but pair naturality still needs a separate argument.
The geometric hypotheses let the existing integral internal-Hom closure theorem
settle the witness domain without a new faithfully flat descent proof.

The outside-unit tools are normalized partial-closed existence/uniqueness and
`lem-sf-derived-complete-legacy-comparison`. The two new nodes use the existing
normalized rational evaluation naturality, localized braiding naturality and
faithful coherent reduction as generic coefficient tools. No realized step of
`sk-prop-sf-biduality-general` is bypassed; its realized list is empty. Maintainer
tool-use approvals have not been added or reordered. There are no forced
adaptations and no target or definition changes.

## New nodes

`lem-sf-normalized-common-evaluation-naturality` now attaches to
`Sheaf.Paper.NormalizedCommonEvaluationForStructure`, with declaration
`WeilConjectures.normalizedCommonEvaluationForStructure_naturality`. The generic
statement is unchanged apart from its declaration name. Its proof represents the
pair arrow and evaluations at a common finite field, uses normalized rational
evaluation naturality and cancels the specified comparisons. Its single named
hole retains a complete proof in words and source citation.

`lem-sf-common-tensor-braiding-naturality` attaches to
`Sheaf.Paper.CommonTensorBraidingNaturality`, with declaration
`WeilConjectures.commonTensorBraiding_naturality`. It retains the returned statement,
named hole and proof: faithful coherent reduction gives integral naturality,
localization gives rational naturality, and the prescribed representative formulas
give common-stage naturality.

Both nodes refine the assigned node's original step 6. Their edge cases include
zero and identity arrows, unequal entry fields, localized sums and arrows killed
only after scalar extension; neither argument uses injectivity of individual
transitions. Sources, searches, dependencies and exact Lean records are included.
There are no change records because no existing signature or definition changes.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
