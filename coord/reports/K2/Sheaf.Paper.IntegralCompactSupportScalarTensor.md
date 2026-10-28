## What changed

Proved `WeilConjectures.PurCompactSupport.scalarTensor_exists` by applying the
existing `tensorComparisonDescent` theorem to the signed scalar total comparison.
The supporting private proofs establish preservation of flat K-flat representatives,
closure under total tensor, and invertibility of the specified scalar counit.

Proved `WeilConjectures.PurCompactSupport.scalarTensor_unique` by faithful restriction
to resolving pairs and cancellation of the representative and scalar counit maps.
The existing signatures, normalization equations and chosen comparison are preserved.
The two obligation nodes now record these actual proofs and dependencies.
Local irreducibility of total-complex constructors avoids unnecessary unfolding.
The counit natural transformation uses the specified `pbcComplexCounit` directly
on components, with naturality supplied by the existing cochain counit theorem.

Validation: the final remote single-file compilation passed with exit code 0,
no warnings and no `sorry`, in 58.9 seconds. The import-direction checks for the
representative descent data and total-tensor model passed. The delivery tool runs
its required axiom probe and preflight before pushing.

## Proved and sorry left

Closed 2 existing holes:

- `WeilConjectures.PurCompactSupport.scalarTensor_exists`
  (`new-sf-scalar-tensor-existence`).
- `WeilConjectures.PurCompactSupport.scalarTensor_unique`
  (`new-sf-scalar-tensor-uniqueness`).

No holes added or split off. No `sorry` remains in the item.
These are proofs from existing declared dependencies, not a claim that every
transitive dependency of those declarations is already proved.

## No longer needed

No original Lean import or module is pruned. The generic coefficient-data node
`def-pur-integral-compact-support-coefficient-data` is replaced in the two obligation
nodes' `proof_deps` by the precise scalar-extension, K-flat and descent lemmas used.
It remains their statement dependency and remains imported by the item. The existing
signed-total and resolving-representative route suffices; no new mathematical
obligation is needed. All added imports serve the completed proofs.

## Where the brief, the DAG or earlier work was wrong

The current shared queue row lists one hole, but the assigned source contains the two
named existence and uniqueness holes introduced by its preceding decomposition.
Both are addressed. No mathematical statement defect or unit-route departure was found.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralCompactSupportScalarTensor": "9915e4201096c042117fe411ec45a625e279c552"}, "own_failed": ["Sheaf.Paper.IntegralCompactSupportScalarTensor"], "results": {}, "time": "2026-10-28T07:58:27+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
