## What changed

The target module now imports two proof-only helper modules and proves
`native_exceptional_ordinary_counit` by combining their conclusions. The first
helper isolates existence of the ordinary comparison isomorphism. The second
fixes that comparison and isolates the ordinary counit carrier, invariant
zero-shift class, and all graded Hom bijections. Both helper declarations are
new split-off nodes with documented proof plans.

## Proved and sorry left

The target theorem `WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit`
is proved by a real constructor and application of the two strict subclaims.
Two new proof obligations remain as named declarations:

- `native_exceptional_ordinary_counit_comparison` in
  `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison` (node
  `lem-sf-native-exceptional-ordinary-counit-comparison`), whose conclusion is
  only existence of the comparison isomorphism.
- `native_exceptional_ordinary_counit_witness` in
  `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness` (node
  `lem-sf-native-exceptional-ordinary-counit-witness`), whose comparison
  isomorphism is fixed input and whose conclusion supplies the remaining
  witness and graded bijections.

Thus one target sorry is closed and two strictly smaller sorries are added by
decomposition; no sorry occurs in a definition.

## No longer needed

No import is removed. The original geometric proof dependencies are retained
as dependencies of the two split-off statements, while the target module's
completed proof depends directly only on the two helper modules and its
existing `NativeExceptionalHomTransport` import. No existing DAG node or
module is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's single proof plan is mathematically consistent but too large to
encode directly in this module because the parent counit-square module already
imports it, preventing use of the parent theorem as a shortcut. The proof is
therefore decomposed into the comparison component and the fixed-comparison
ordinary witness component. Their conjunction is strictly stronger than either
subclaim and exactly reconstructs the original target statement.

## New nodes

`lem-sf-native-exceptional-ordinary-counit-comparison` records the comparison
isomorphism substatement and its source-level construction. Its Lean module is
`lean/Sheaf/WeilSheaf/NativeExceptionalOrdinaryCounitComparison.lean`.

`lem-sf-native-exceptional-ordinary-counit-witness` records the fixed-comparison
witness, invariance, and graded bijection substatement. Its Lean module is
`lean/Sheaf/WeilSheaf/NativeExceptionalOrdinaryCounitWitness.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit": "38d8da350553c21ab8acf4601f5ef60e14e4c474", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison": "26ba422a92afc87589cff07312e37d42ac197d32", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": "6d9ff825e9bb3fda66d8f1af50c3c594981792d5"}, "results": {}, "time": "2026-10-28T04:24:08+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
