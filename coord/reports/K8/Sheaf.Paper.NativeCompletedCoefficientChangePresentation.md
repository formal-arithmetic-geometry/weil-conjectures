## What changed

Added `Sheaf.Paper.NativeCompletedCoefficientPresentationAt`, which states the
fixed-scheme normalized presentation construction as a split-off theorem.  The
assigned module now imports it, chooses one presentation for every scheme, and
sets each completed-to-native map to that presentation's `integralMap`; the
family equality is proved by reflexivity.  The assigned node's proof and
`proof_deps` were updated to record this route, and a node was added for the
split-off theorem.

## Proved and sorry left

Proved `WeilConjectures.LocallyFiniteAdicCompactSupport.exists_native_completed_coefficient_presentation`
from the fixed-scheme theorem.  One split-off `sorry` remains in
`WeilConjectures.LocallyFiniteAdicCompactSupport.exists_native_completed_coefficient_presentation_at`,
recorded by node `lem-sf-native-completed-coefficient-presentation-at`.

## No longer needed

None.  The parent proof uses the fixed-scheme presentation node; its original
data dependencies are retained by that node.

## Where the brief, the DAG or earlier work was wrong

The parent DAG proof described the finite quotient construction but supplied no
Lean declaration that constructs a `CoefficientPresentation` at a fixed scheme.
The missing construction is isolated as the strictly smaller pointwise theorem
above, while the family assembly is fully proved in Lean.

## New nodes

`lem-sf-native-completed-coefficient-presentation-at` records the fixed-scheme
normalized presentation construction and its remaining proof obligation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompletedCoefficientChangePresentation": "fc9b9a457dff057dc37655a38cb7360155eb732a", "Sheaf.Paper.NativeCompletedCoefficientPresentationAt": "2eadf6608d00f5bfd8bedc2599b27ae8633c7d9f"}, "results": {}, "time": "2026-10-28T07:54:55+0800", "transitive": 0, "version": 1}
```

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
