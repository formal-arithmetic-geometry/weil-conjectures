## What changed

Filled `WeilConjectures.nativeProperDerivedPresentation` in
`Sheaf.Paper.NativeProperDerivedPresentation`. The proof imports the existing
normalized comparison `Sheaf.SixFunctors.IntegralNativeDirectComparison`,
instantiates it with `o.direct f` and `o.evaluation f`, and uses its canonical
`integralNativeDirectIso`. The existing public imports and declarations retain
their interfaces; the added import is proof-only.

Validation: the module compiles with `lcompile.py` in 6.4 seconds with no errors or warnings.

## Proved and sorry left

Closed: `WeilConjectures.nativeProperDerivedPresentation`, the item's one
original sorry (node `lem-native-proper-derived-presentation`). Added: zero
holes. Remaining in the item: zero holes. No split-off statements.

The reused theorem
`WeilConjectures.IntegralSystemRealization.integralNativeDirectComparison`
(node `lem-sf-integral-native-direct-comparison`) has an existing `sorry` in its
own module. It is unchanged by this delivery. This closes the assigned module's
hole from an existing declared dependency; it does not establish that dependency
without `sorry`.

## No longer needed

No existing import, module or declaration is removed. The planned direct proof
dependencies for constructing the section comparison, derived comparison, and
mate normalization are subsumed by the existing stated
`lem-sf-integral-native-direct-comparison`; they are no longer direct proof
dependencies of this item: `def-pur-completed-pullback-tower-core`,
`lem-pur-coefficient-system-unbounded-comparison`,
`def-strict-coefficient-pullback-evaluation-data`, and
`def-sp-varying-ring-operations`.

## Where the brief, the DAG or earlier work was wrong

The DAG's planned proof duplicated the normalized native direct comparison
already present in `IntegralNativeDirectComparison`. Reusing that theorem is a
shorter route and preserves the exact evaluation normalization.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
