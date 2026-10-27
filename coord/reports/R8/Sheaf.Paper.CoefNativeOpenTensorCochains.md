## What changed

Retained and repaired the earlier packet. `nativeOpenTensor_cochains_exists` now
combines the sequence-site existence result with the finite result for each n.
The proof eliminates the first existential and uses dependent choice only to
assemble the family of finite witnesses. Its statement, binders and universes
are unchanged.

The two original specialization bodies are factored verbatim into
`CoefNativeOpenTensorPrimitives`. `SystemOpenCochains` and `FiniteOpenCochains`
remain transparent aliases of exactly those types. Both original public imports
remain; the new primitive import supplies the alias bodies. The two existence
imports are private proof imports. No other existing Lean module is changed.
The definition factorization is documented in
`coord/changes/coef-native-open-tensor-primitives.md`.

Expanded both split-off docstrings into field-by-field construction arguments,
with native adjunction identification, tensor normalization, K-flat preservation,
signed totalization and naturality. Added the missing definition node and actual
LeanSearch, LeanFinder, Loogle and Mathlib grep records. The two new statements
are the two independent clauses of the original conclusion: neither implies
its other clause, and the parent proof performs the simultaneous assembly.

## Proved and sorry left

Closed the one direct hole in
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_cochains_exists`
(node `lem-coef-native-open-tensor-cochains`) by decomposition, not by a
complete proof of the mathematical construction. The item itself has zero
remaining direct sorries. Two holes are added, in strictly smaller statements:

- `WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_system_exists`
  (`lem-coef-native-open-tensor-system-existence`): only the sequence-site datum;
  it asserts no finite-stage datum or family.
- `WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_finite_exists`
  (`lem-coef-native-open-tensor-finite-existence`): only a datum at one fixed n;
  it asserts no sequence-site datum or simultaneous family over n.

Thus one upper hole is closed, two lower holes remain, and the net is -1.
No primitive abbreviation contains a sorry or chooses data from an existence
statement. The existential witnesses are chosen only inside the parent theorem.

## No longer needed

None. No module or node is withdrawn or pruned. Both original public imports
are retained for the public API. All six original mathematical dependencies
remain in the two construction nodes; the parent's immediate proof dependencies
are now the two independent existence lemmas. The existing localization,
localized exact adjunction, K-flat pullback, ringed-slice tensor, normalization,
and total-tensor theorems do not directly have the fixed native specialization
as their conclusion. Their transports and compatibility equations remain the
work recorded in the two split-off statements.

## Where the brief, the DAG or earlier work was wrong

The retained packet lacked a node for its new primitives module, complete
Mathlib search records, a change record for the specialization aliases, and
complete proof descriptions for its split-off lemmas. The required first
check found the missing-node gate; all these packet defects are repaired.
The earlier claim that the item was no longer queued is not current: the server
lists it as a stage-3 proof item, with no build-error or rework record.

The parent construction has no relation equating its sequence witness with
its separately requested finite witnesses. Separating these clauses therefore
requires no new compatibility hypothesis. Neither the unit route nor any target
statement changes. Checked the empty open, zero coefficient ring, n=0 as the
first positive quotient, and unbounded direct-sum totalization: these impose
no extra assumptions on either new statement.

## New nodes

`def-coef-native-open-tensor-primitives` records the two explicit specialized
types in `CoefNativeOpenTensorPrimitives`; these are the original expressions,
not new chosen objects. The change record is
`coord/changes/coef-native-open-tensor-primitives.md`.

`lem-coef-native-open-tensor-system-existence` records just the sequence-site
construction, including its horizontal coefficient arrows.

`lem-coef-native-open-tensor-finite-existence` records the construction at a
single fixed positive quotient stage. Both statements have complete construction
arguments in their docstrings, and their DAG proofs retain the original four
construction steps and six declared mathematical dependencies.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefNativeOpenTensorCochains": "24883058d4c98279a981a16746182cd98d71edaa", "Sheaf.Paper.CoefNativeOpenTensorFiniteExistence": "5bf5842d94f4a597284aad28b63bcaabe778d03a", "Sheaf.Paper.CoefNativeOpenTensorPrimitives": "19d18618f6d9a1a0942303dda6fb3caff18388cc", "Sheaf.Paper.CoefNativeOpenTensorSystemExistence": "b87fdcf5a4178f15c1e58064743faf3be5e30a44"}, "results": {"Sheaf.Paper.CoefNativeOpenTensorModelsDataExistence": {"hash": "1edb30173f46503bb1ca97ba51b72d14a54ece98", "status": "OK"}}, "seconds": 20, "time": "2026-10-28T00:27:21+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
