## What changed

Repaired `WeilConjectures.LocallyFiniteAdicCompactSupport.native_compact_support_geometry`.
The native commutativity helper now explicitly installs the commutative constant-sheaf
instance, the braided forgetful functor from `WeilCoefficients` to abelian groups, and the
braided sheaf-composition instance before applying `Functor.isCommMonObj_obj`. Added the
proof-only import of `WeilConjectures.SixFunctors.ProEtale.Adic.Hom` for the constant-sheaf
commutativity instance.

## Proved and sorry left

The module's only theorem, `native_compact_support_geometry`, is proved with no `sorry` left.
No new `sorry` declarations were added.

## No longer needed

None. The existing imports and DAG dependencies remain required by the construction.

## Where the brief, the DAG or earlier work was wrong

The earlier proof used `infer_instance` for native commutativity. In the current import
closure, inference does not discover the braided forgetful structure or the commutativity
instance automatically, so the helper failed during the global build. The theorem statement
and DAG route are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportGeometry": "a56d3985d7f5873b6a64164e7b4be9ff6b77ca70"}, "results": {}, "time": "2026-10-28T06:26:25+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
