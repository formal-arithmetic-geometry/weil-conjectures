## What changed

Proved `AlgebraicGeometry.Proj.scalarExtension_twist_canonical_section` in
`Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCanonicalSection`.
Mathlib's `Adjunction.unit_leftAdjointUniq_hom_app` identifies the normalized
identity comparison on adjunction units. Evaluating on the given section,
using the chosen adjunction's section normalization, and evaluating at the
specified point proves the result. Updated the item's DAG proof to record
these steps. Existing signatures, definitions, docstrings and imports are unchanged.

Validation: the changed module compiles through `lcompile.py` in 3.9 seconds.
No other existing module changes, so no consumer adaptation is required.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Proj.scalarExtension_twist_canonical_section`
(node `lem-sfb-proj-scalar-extension-twist-canonical-section`).
One hole closed, zero added, zero remaining in the delivered module.
No split-off statements or new declarations.

## No longer needed

None. No imports were added or removed. Both original statement dependencies
remain needed. The existing route and unit route are preserved; no modules
or DAG nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing normalized adjunction and
Mathlib's compatibility of left-adjoint uniqueness with units suffice to close
this obligation directly. No further decomposition is needed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCanonicalSection": "75304770e86310f38496ef0a5d2c79d91e86c16e"}, "results": {}, "time": "2026-10-28T10:17:06+0800", "transitive": 0, "version": 1}
```

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
