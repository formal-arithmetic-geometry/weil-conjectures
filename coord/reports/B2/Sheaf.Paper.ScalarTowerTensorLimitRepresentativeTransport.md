## What changed

Corrected the already disputed arbitrary-bridge assertion in
`Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport`. It now asserts the
ordinary-source equation for the specified `scalarTensorOrdinary` followed by the
tensor of the two `scalarCompletion` maps. The other word is precomposed by source
completion. No arbitrary bridge remains in the theorem.

Proved the private `scalarTensorCompleted_unitEquation`, independently of the
remaining hole. Repaired the unclaimed
`Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly`: its premise is exactly
the corrected representative equation. Its new complete proof transports two
natural transformations along the essentially surjective product localization and
cancels scalar completion on the complete tensor. Its completed canonical conclusion
is unchanged. Added one private proof import of the item for the proved helper.

The existing `ScalarTowerTensorLimitTransportAssembly` application needs no source
change; it is checked against both repaired statements. Updated both node statements,
Lean signatures, proof records and statement-change records. The independent reader
should assess this as a substantive statement repair, not a proof of the old false
universal bridge assertion.

## Proved and sorry left

Closed **0 of 1** original item holes; added **0** holes; split off **0** statements.
This delivery repairs a false quantifier and its transport, and does not count the
corrected normalization statement as proved or decomposed.

The one remaining hole is
`WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_on_good_representatives`
(node `stage3-pur-scalar-tensor-limit-good-representatives`). Its statement has been
corrected in place; its proof remains exactly `by sorry`, with a full source/proof
docstring. The strict normalized representative calculation is still needed.

Fully proved in this delivery:
- private `scalarTensorCompleted_unitEquation` in the item;
- private `transport_natural_eq` in the assembly;
- the corrected implication
  `scalarTowerTensorLimitSquare_of_representativeTransport`, with zero holes.

The old two private vanishing diagnostics remain proved. No new module, unproved
helper, axiom, definition, instance or attribute is added.

## No longer needed

No module or public import is pruned. The old private `transport_all_bridges`
helper is replaced by ordinary natural-transformation equality transport. No
hypothesis about arbitrary bridge maps is used. The K-flat and normalization nodes
remain needed for the single retained normalization hole; they are not declared
pruned just because the current transport proof is categorical.

The assembly node's dangling
`stage3-pur-scalar-tensor-limit-strict-equation-predicate` statement dependency has
no node file (already reported by A8). Its signature infrastructure is supplied by
the existing strict-witness data module, recorded instead in this repair. No DAG
node or source-library declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The old assertion asked for beta followed by a fixed map to equal another fixed
map for every beta. Its existing formal diagnostic shows that, when the bridge
objects are isomorphic, this forces both fixed maps to vanish. Stacks 07A4 fixes
the canonical tensor comparison; it does not assert that every map is that
comparison. A7 reported the defect but retained the false assertion. This repair
prescribes the actual map and updates its consumer rather than repeating that
report or moving its hole elsewhere.

The natural square must be stated before inverting completion: completeness is
not available on arbitrary good representatives. The ordinary-source formulation
is natural on all derived objects and has exactly the required canonical completed
specialization. Cancelling source completion uses the given `hT`; the complete
input maps give the prescribed `scalarTensorCompleted` component by its definition.
Zero inputs and the empty scheme satisfy the same natural equation. Identity
coefficients and ramification retain the same specified chain and quotient maps;
there is no zero-map bridge claim or flatness assumption on quotient ring maps.

The shared and current server records were read: this is a one-hole disputed
stage-3 proof item, with no build-error or rework record. Both assembly modules
were unclaimed when checked. No unit statement or route is changed; the unit has
no realized step attached to these split nodes.

## Statement corrected

For `stage3-pur-scalar-tensor-limit-good-representatives`, the bridge quantifier is
replaced by the specified ordinary tensor/completion composite, with source
completion on the other side. Its recorded citer is
`stage3-pur-scalar-tensor-limit-transport-assembly`; its statement and exact proof
application still hold using the corrected implication.

For `stage3-pur-scalar-tensor-limit-strict-equation-assembly`, only the representative
premise changes; the completed canonical conclusion and other hypotheses stay the
same. Its recorded citer is also
`stage3-pur-scalar-tensor-limit-transport-assembly`, preserved without edits.

Change records:
- `coord/changes/B2-ScalarTowerTensorLimitRepresentativeTransport-canonical-source.md`
- `coord/changes/B2-ScalarTowerTensorLimitStrictEquationAssembly-canonical-source.md`

Validation through `lcompile.py`: the corrected item compiled without messages in
10.9 seconds, the corrected strict-equation assembly in 17.0 seconds, and the
unchanged direct caller in 8.9 seconds, in dependency order. The unchanged caller
copy was removed from the sandbox after this check. The delivery tool additionally
checks the declarations, axioms, node records and related-module compatibility.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport": "20e426a0fa983f4c6be7d52c187c13b526894929", "Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly": "8e26aae0372bde23110909a9aa0c5e0b5fcdf4cf"}, "results": {"Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly": {"hash": "852ed0565aa9cc152bba17a7f1cbc31a07ff28bd", "status": "OK"}}, "seconds": 80, "time": "2026-10-28T12:05:49+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
