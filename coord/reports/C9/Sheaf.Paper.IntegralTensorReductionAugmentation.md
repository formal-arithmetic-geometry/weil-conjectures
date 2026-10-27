## What changed

Filled IntegralOrdinary.tensorReductionAugmentation_exists using existing normalized
ringed tensor models, the existing tensor_augmentation_onGood helper of
PrimitiveQuotientAugmentations (proved using tensorQuotientTranspose_onGood), and
fully faithful descent
along the product good-complex localization. The comparison of ordinary tensors
preserves their specified representative maps. Composing it with tensorClosed and
reductionTensor constructs the required isomorphism. The canonical ringed tensor
augmentation is transported along that comparison, and its full chain normalization
identifies it with every TensorAugmentationNormalized transformation. Naturality of
the adjunction unit and localization faithfulness give the required equation on all
ambient derived objects.

Validation: lcompile.py --all compiled the new comparison module in 16.5 seconds,
the chain identification in 14.1 seconds, and the item in 51.8 seconds, all with
exit code 0 and no warnings. No profiler options remain.

All existing declaration signatures, definitions, attributes and public imports are
preserved. The two public representative lemmas are proved in new modules
OrdinaryTensorRingedModelComparison and TensorCompletionChainRingedIdentification,
with their own nodes. Their generic categorical helper is private and fully proved.
No other existing module or node and no source-library module is changed.
All added imports in the item serve proofs. The node records the existing transpose calculation used by the proof.
After factoring the abstract localization argument and locally preventing
unnecessary unfolding, the combined file still exceeded 60 seconds in checking.
The two self-contained proved representative lemmas therefore have separate
compilation boundaries. No mathematical obligation was moved to a new hole.
RingedModels existence and its tensor transpose are used as generic normalized
model and map-computation tools; no projection-formula or coherence unit statement
is bypassed.

## Proved and sorry left

Closed: WeilConjectures.IntegralOrdinary.tensorReductionAugmentation_exists
(node lem-sf-tensor-reduction-augmentation), the sole original hole.

Added holes: none. Sorries left in the item or either new module: none.
New proved declarations: tensorRingedModelComparison
(node lem-sf-ordinary-tensor-ringed-model-comparison) and
ringedTensorChain_eq_tensorCompletionChain
(node lem-sf-ringed-tensor-completion-chain-identification).
Split-off unfinished theorems: none.
The existing tensorReductionAugmentation_existsUnique proof and the definition
selecting the unique comparison remain unchanged. The proof uses existing stated
library dependencies; this is not a claim that those dependencies are all free of
sorry axioms.

## No longer needed

No existing public imports, nodes or modules are withdrawn. The direct proof import
of RingedTensorChainIdentification is now used inside the new chain-identification
module and remains a transitive dependency. The strict scalar and Roos
coordinate calculation already exists in tensorQuotientTranspose_onGood, so this
delivery needs no new unfinished statement and no repeated construction of that
calculation. The old proof dependencies remain needed either directly or within the
existing normalized models and transpose calculation. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan did not cite the existing RingedModels tensor transpose
calculation. Its representative normalization and the full-coordinate uniqueness
of the strict tensor chain allow a proof by transport and localization, with no new
mathematical obligation. The current server queue row was checked: stage 3, one
hole, proof/route; there was no rework row or build-error file for this item.
The zero complex and empty scheme require no separate existence assumptions: all
comparisons and localization arguments apply uniformly to these cases.

## New nodes

lem-sf-ordinary-tensor-ringed-model-comparison: the ordinary tensor and any supplied
RingedModels tensor have a representative-normalized natural isomorphism. Proved
using the product good-complex localization and Mathlib fully faithful whiskering.
It asserts neither strong reduction nor an augmentation equation after taking a
limit. Source: Stacks 07A4 and 06YS, specialized to the existing models.

lem-sf-ringed-tensor-completion-chain-identification: the supplied ringed chain and
the specified tensor completion chain have equal components on arbitrary cochain
complexes. Proved from full-coordinate uniqueness and the two existing component
formulas. Source: Stacks 07A4 and 0941, with the existing strict augmentation
normalization. Both nodes record three actual Mathlib searches. No change record
is needed: existing public declarations and their definitions are preserved.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.IntegralTensorReductionAugmentation": "52c812bc6b1f1a034f5c38e845038fdccc13332c", "Sheaf.Paper.OrdinaryTensorRingedModelComparison": "530f9eb0c81fc012b3dc1ee3610c547e68e44839", "Sheaf.Paper.TensorCompletionChainRingedIdentification": "76e7e06524e8c06a45510b2ab4369df3370485e0"}, "results": {"Sheaf.Paper.IntegralReductionTensorPullback": {"hash": "ec50c031e51891d8b934a3a937859dc78eb882a9", "status": "OK"}, "Sheaf.Paper.IntegralTensorPullbackAugmentation": {"hash": "460d419d690ace16bd39462050cf1a9224aff152", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T04:26:27+0800", "transitive": 0, "version": 1}
```

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
