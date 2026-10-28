## What changed

Proved `WeilConjectures.completedConstantSquare_isPushout` in its existing module,
with its signature and existing docstring unchanged. Added private proved helpers and proof imports. Replaced the public import of
NativeConstantSupportModel by ConstantScalarTowerAdjunction, which supplies the
constant coefficient definitions used by the statement. The proof uses an integral basis, the normalized
constant and completed finite-sum formulas, and the canonical tensor-product
pushout. Finite projections identify the generic adic maps with the exact maps
in the statement. Updated the item's DAG proof and proof dependencies accordingly.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.completedConstantSquare_isPushout`
(node `new-completed-constant-square-pushout`). No new holes; no split-off
statements; no `sorry` remains in the delivered module. All new helpers are private
and proved. No existing definition or public signature changed.

## No longer needed

None of the three original dependency modules is pruned: the adic-basis API
supplies the normalized completed sum, CompletedIntegralFiniteFree supplies the
integral basis, ramification and quotient presentations, and
FiniteFreeCompletedScalarComparison supplies the canonical coefficient map and
its projection characterization. The derived-comparison portion of the last
module is not invoked. Removed the unused NativeConstantSupportModel import, replacing it with its
ConstantScalarTowerAdjunction dependency. This removes no module globally: the
sole direct consumer independently imports NativeConstantSupportModel. The
constant specified basis API is an additional direct proof dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The completed finite-free theorem's bare
existence of a module isomorphism does not on its own give the pushout: the
identification of its basis columns with the images of the constant basis is
essential. The proof uses the normalized construction in AdicBasisLimit instead.
The argument covers zero section rings without a nontriviality assumption.

Validation: the final module compiled in 21.2 seconds after import cleanup.
The original theorem signature and docstring match verbatim; the module has zero
`sorry`s and every line is at most 100 characters. Delivery also checks the
direct consumer against the final imports.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompletedConstantSquarePushout": "c1790eb675a8e5354ce9daf0f0fe88a1fbac9525"}, "results": {"Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence": {"hash": "25c366fb9d337136da1712745c964d938e66e150", "status": "OK"}}, "seconds": 48, "time": "2026-10-28T12:13:16+0800", "transitive": 0, "version": 1}
```

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
