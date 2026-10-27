## What changed

Moved the completed-model vocabulary definitions into the public base module
`Sheaf.Paper.IsomorphismScalarCompletedModelBase`. Added two strictly smaller
statement modules, one for existence of the normalized completed comparison and
one for preservation of the three model clauses. The item module now publicly
re-exports the vocabulary and combines those two component statements to prove
`scalar_completed_model`.

## Proved and sorry left

Closed the `scalar_completed_model` hole by conjunction of the two component
results. The delivery adds the intentional split-off holes
`scalar_completed_formula` (node
`lem-weil-isomorphism-scalar-completed-formula`) and
`scalar_completed_preserves_models` (node
`lem-weil-isomorphism-scalar-completed-preserves-models`). The base vocabulary
module contains no holes.

## No longer needed

The final wrapper no longer needs the six proof imports directly; they remain
publicly imported by the base vocabulary module because its definitions use
those declarations. No proof dependency was pruned from the completed-model
route: the two split statements cite the limit comparison, inverse-image
comparison, scalar-extension, and ringed-topos K-flat declarations recorded in
their nodes.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan bundled the normalized completed tensor
isomorphism and model-preservation argument into one theorem, although the two
parts have independent constructions and could not be discharged by the
available declarations in one wrapper. The route is therefore represented by
two strictly smaller component nodes. The vocabulary extraction preserves all
original public definitions and signatures.

## New nodes

`def-weil-isomorphism-scalar-completed-model-vocabulary` records the moved
vocabulary module. `lem-weil-isomorphism-scalar-completed-formula` records the
completed pure-tensor comparison component. `lem-weil-isomorphism-scalar-completed-preserves-models`
records the model-preservation component.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarCompletedModel": "585dfb5ef8a5dc6abaee39f03b64c93d62846be9", "Sheaf.Paper.IsomorphismScalarCompletedModelBase": "13afc170f5ad7d40aa0444d95d865e2d49f008d6", "Sheaf.Paper.IsomorphismScalarCompletedModelFormula": "6f72994dd71c42f2d41dcc5fc332ddb9541ad5d3", "Sheaf.Paper.IsomorphismScalarCompletedPreservesModels": "8838d362bfcd3d9473ea830bb9a8820df493cc4c"}, "results": {"Sheaf.Paper.IsomorphismScalarFiniteCore": {"hash": "d58b960024b316751fd25c32bf9b82eaa8741589", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarFiniteModel": {"hash": "0dcc5e65202ae1d289475af3f9a3e2f06f593c24", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarTensorKFlatModel": {"hash": "327a4898e867eaaef95b8967d5dc5396edb734cb", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T07:14:07+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
