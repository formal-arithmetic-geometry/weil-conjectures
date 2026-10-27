## What changed

Proved `integralTensorLeftShift_existsUnique`, preserving its signature and the
meaning of its normalization predicate. The proof constructs the unsigned
finite comparison, identifies its conjugated quotient transitions by their
generator formula, assembles the tower, and applies the existing signed
product/cone/Roos construction and good-model descent. Uniqueness uses pure
tensors, cone injections, cancellation and localization extensionality. The
restriction calculation compares arbitrary lifts, keeping their constructions
out of the generator argument.

Added three proof imports exposing existing private helpers; public imports
are unchanged. Updated the existing proof node's route and dependencies.
In the unclaimed `IntegralTensorShiftProperties`, changed `tensorShiftFirst`
from `def` to `abbrev`, preserving its type and body. The new generic
`integralTensorLeftModelProperty` factors the normalization through coefficient,
tower and descent data; `integralTensorLeftProperty` abbreviates its canonical
specialization. This avoids repeatedly unfolding the concrete constructions.
The new definition is attached to the existing shift-properties node.

The complete original predicate and its new specialization were checked by
`Iff.rfl` against the patched dependency. The current direct consumers
`IntegralOperationShiftData`, `SystemTensorLeftShiftUnique` and
`SystemTensorShiftRepresentativeModels` compiled unchanged against that
dependency. No consumer is adapted; the two quarantined users are preserved.
Both delivered modules passed the complete packet compilation before the local
instance helpers were made private. Their proof bodies are unchanged from that
passing version. Delivery validation of the visibility cleanup is blocked by
missing shared compiled dependencies. The finite section
formula is proved
with abstract coefficients before its canonical specialization; the pointwise
finite comparison is a component of the natural comparison.

Change records: `coord/changes/A8-first-tensor-shift-wrapper-reducibility.md`,
`coord/changes/A8-integral-left-property-reducibility.md`, and
`coord/changes/A8-integral-left-model-property.md`.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.integralTensorLeftShift_existsUnique`
(node `lem-pur-integral-tensor-left-shift-unique`). All added private helpers are
proved. No `sorry` remains in the assigned module or either delivered module:
1 closed, 0 added, 0 split off.

## No longer needed

None. No existing import, declaration, node or module is withdrawn. The original
K-flat-resolution dependency remains through the good-model localization tools.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The generic product/cone and localization
helpers already proved in `CompletedTensorShiftRight` apply without the
invertibility hypothesis of that module's public right-slot theorem. Reusing
those helpers implements the node's plan for arbitrary schemes.

Delivery tooling cached a missing-`Subobject.olean` failure even after the local
artifact reappeared; its dependency key uses the older published-build stamp.
A fresh complete-packet request then failed at the first import on missing
`WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent.olean`, before
checking the assigned proof. No launcher file or compiler cache was changed.
Nothing was pushed. The optional, unvalidated tower-formula optimization was
reverted, preserving the proof body that passed complete-packet compilation.

Resumed attempt, 2026-10-26: the required initial `deliver3.py` check
returned the cached missing-`Subobject.olean` failure (69.6 s), with nothing
pushed. A fresh complete-packet `lcompile.py --all` request
(`ba51f2b824f124b0bbab57d2`) finished with exit code 1 at the first import:
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale.olean` was missing
from the shared compiled library. It did not check either delivered module.
This was an import-artifact failure, not a proof elaboration timeout. No
launcher script, compiler cache, shared source, or Lean proof was changed.

Rechecked the current downstream declaration users. Three additional users of
`tensorShiftFirst` now exist: `CompletedTensorShiftAddOnGood`,
`CompletedTensorSlotShiftLaws`, and `IndependentExpressionShiftNaturality`
(all under `Sheaf.SixFunctors`). The first also uses
`integralTensorLeftProperty`. Their interfaces retain the identical meaning;
the change-record user tables now list them and current holders. The two
quarantined users remain preserved. The resumed compiler failure prevents
additional consumer validation. The saved proof packet is retained intact.

Next resumed attempt, 2026-10-26: the required initial delivery check again
returned the cached missing-`Subobject.olean` error (69.6 s), with nothing
pushed. The supported complete-packet compile returned the existing result
`ba51f2b824f124b0bbab57d2`: missing
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale.olean` at the first
import (exit code 1, 60.0 s). Neither delivered module was checked. These are
cached dependency-artifact failures, not new proof diagnostics or elaboration
timeouts. The Lean packet, launcher tools, caches and shared repository were
left unchanged.

Further resumed attempt, 2026-10-26: the required initial `deliver3.py`
check exited 1 with the missing shared `Subobject.olean` diagnostic (69.6 s).
The complete-packet `lcompile.py --all` call reattached to result
`ba51f2b824f124b0bbab57d2` and exited 1 with missing shared `Etale.olean`
(60.0 s). Both outputs mark `IntegralTensorShiftProperties` as NOT compiled;
neither delivered module was checked, and nothing was pushed. Rechecked the
current sources and downstream declaration users: eight users of
`tensorShiftFirst` and four of `integralTensorLeftProperty`, as covered by the
existing change records. No Lean file, node, launcher script, shared source,
or compiler cache was changed in this attempt. The proof packet is preserved.

Final resumed attempt, 2026-10-26: the required initial delivery check again
exited 1 with missing shared `Subobject.olean`, before compiling either module;
nothing was pushed. The supported `lcompile.py --all` command reattached to
result `ba51f2b824f124b0bbab57d2` and returned exit code 1 with missing shared
`Etale.olean`, also before checking either module. These are dependency-artifact
failures, not proof diagnostics or elaboration timeouts. The existing Lean
packet and node changes remain intact. No launcher tool, compiler cache or
shared source was changed.

Current resumed attempt, 2026-10-26: the required initial delivery check
returned exit code 1 with the cached missing shared `Subobject.olean` diagnostic
(69.6 s). The supported complete-packet compile reattached to result
`ba51f2b824f124b0bbab57d2` and returned exit code 1 with missing shared
`Etale.olean` (60.0 s). Both explicitly report the dependency module as NOT
compiled, before checking the assigned proof; nothing was pushed. Rechecked
the current dependency diff and declaration users: eight current modules use
`tensorShiftFirst`, four use `integralTensorLeftProperty`, all covered by the
retained change records. Both packet Lean files still contain zero `sorry`
tokens. No Lean file, DAG node, shared source, launcher tool, or compiler cache
was changed. The packet is preserved pending repair of the shared build or its
published-artifact cache by the tooling owner.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
