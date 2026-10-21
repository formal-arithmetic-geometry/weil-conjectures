## What changed

Repair of reviewer C-63948, returned head 6394859d9, using the explicitly permitted
option (b). Keep `ProEtaleConstantReductionModels` with its six closed original holes,
its coupled universal reduction/counit data, normalized augmentation and exact-pullback
comparison. The item publicly reexports Models and preserves all original public
signatures and its generic completion-mate alias. Leave `projection_isIso` as its
original named theorem with `sorry`.

Remove the unlanded `ConstantProjectionNormalization`,
`PerfectConstantProjectionChainModel` and `PerfectConstantProjectionEvaluation` modules
and their three new nodes from the packet. Remove the projection-evaluation import and
its now-unused private conservativity helper. The item-node update still records Models;
its extra reference to the omitted evaluated-projection route is removed. The original
projection proof plan is retained. No target or adopted source-library file changes.

Models and `def-sp-constant-reduction-models` are preserved from the returned packet as
requested. The retained semantic content of `coord/changes/T1-constant-reduction-models.md`
is unchanged; its Users table is extended to cover the current-main textual consumer
inventory after the first preflight requested the missing rows. The change record's earlier references to five files and a completed projection proof
refer to that earlier packet; this report supersedes those historical scope/validation
claims. This repair submits two Lean modules and leaves the projection hole open.

## Proved and sorry left

Six of the seven original holes in the current shared item are closed, with no added
holes. All names below are in `AlgebraicGeometry.Scheme.OrderedExchange`:

- `step_existsUnique`.
- `ordinaryAugmentation_existsUnique`.
- `augmentation_existsUnique`.
- `ordinaryReductionPullInv_isIso`.
- `levelPullIso_transition`.
- `reductionPullIso_existsUnique`.

The retained packet originally copied these six proofs from a richer shared source;
the shared source later synchronized to the seven-hole B3 version. This delivery
preserves those proofs and their elaboration repairs, without claiming their invention.
`reduction_exists` was already proved in the current source and is not counted again.

Exactly one hole remains: `AlgebraicGeometry.Scheme.OrderedExchange.projection_isIso`,
node `lem-sp-completion-mate-comparison`, in the item module. Models has zero holes.
Zero holes are split off or added. The rejected `constantProjectionNormalization` hole
is absent from this repair. No definition or private helper contains a hole.

Validation: `lcompile.py --all` passed for both delivery modules and unchanged copies
of all six current direct importers. The final item compiled in 6.2 s. Consumer times:
`CompletedProjectionCoherence` 12.7 s, `CompletedPullbackUnitTower` 39.7 s,
`OrderedExchangeCoefficientComparison` 54.4 s, `SfCbcExtensionZeroCompletion` 32.8 s,
`CompletedExchangeCoherence` 5.2 s and `SfCbcCompactSupportCompositionLimit` 8.5 s.
The Models module initially compiled in 46.3 s; the follow-up pass reused its compiled
output. All checks exited zero. The six unchanged consumer copies were then removed
from the delivery source set. No forced adaptation is included. A source scan confirmed
that every original public name and its statement text remains, that only the original
projection hole remains, that both DAG records have all dependencies present, and that
every Lean source line is within 100 characters.

Edge cases of the retained constructions require no extra hypotheses: exponent n+1
includes n=0, both zero and unit ideals retain their quotient transitions, and tensor
section extensionality and the universal-model descent cover zero modules and complexes.

## No longer needed

The three unlanded projection modules and nodes named above are omitted under reviewer
option (b), rather than claiming their mathematics is proved or globally unnecessary.
Their plain definitions `constantProjectionTotal` and `constantProjectionTensor` are
also omitted, so no chain-model statement cites a theorem node for definitions. No new
definition node for these omitted definitions is needed. No `deleted.txt` is needed:
none of these six paths exists on the current main branch. No existing library module,
DAG node, upstream declaration or quarantined parent is withdrawn.

The item's `PerfectConstantProjectionEvaluation` proof import is removed. Its original
public imports are publicly reexported through Models. `StrictTowerExchangeMateNormalization`,
`CompletionMateComparison`, `KFlatIndependentCoefficients`,
`KFlatResolutionIndependentCoefficients` and `LeftDerivedFromResolvingClass` remain
needed in Models; moving their imports is not global pruning. The unit's strict quotient
and completed-mate route is preserved.

## Where the brief, the DAG or earlier work was wrong

The reviewer correctly identified that the existential s and t in
`constantProjectionNormalization` were unpinned. With an invertible finite total map,
such a statement is equivalent to the levelwise invertibility being sought. The old
report's claim of a genuine reduction was incorrect. This repair removes that statement
and its consumers and makes no claim that the projection hole has been closed.

The alternative pinned construction would require explicit source and target
comparisons fixed by reduction counits, scalar tensor cancellation, representative
comparison, push/evaluation comparison and the right-derived unit. No arbitrary
comparison isomorphism is introduced in this packet.

## New nodes

`def-sp-constant-reduction-models` is the sole new node. It records the coupled
universal model API, normalized augmentation and exact-pullback construction. Its
module has zero holes. The existing `lem-sp-completion-mate-comparison` retains its
Models reference and original projection argument, with its statement unchanged.
The retained definition-change record is `coord/changes/T1-constant-reduction-models.md`.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
