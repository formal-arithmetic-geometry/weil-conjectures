## What changed

Restored and delivered `lean/Sheaf/AlgebraicGeometry/DerivedPushforwardSquareMateUnit.lean`
from its quarantine path. The existing theorem
`AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit` has its complete categorical
pasting proof, using the existing WeilConjectures declarations
`directImageSquareIso`, `directImageSquareIso_top`,
`directImageSquare_unit_transport`, and `derivedDirectImage_square_mate`.

Removed `derivedPullback` from the file-local irreducibility attribute. The adopted source
library declares `derivedPullback` with `irreducible_def`, so Lean rejects setting the
same status a second time; the local attribute was the reason the restored module could
not compile. This change preserves the public theorem and all imports and does not alter
the statement or any definition.

## Proved and sorry left

Proved the sole declaration in this module,
`AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit`. The module contains zero
`sorry`s and adds no new holes. Its imported transport theorem remains an existing
upstream theorem with its own `sorry` dependency; this delivery does not change it.

## No longer needed

No imports or DAG nodes were pruned. The proof uses all three proof-only imports and the
public affine base-change import. The declared statement dependencies and unit route are
unchanged.

## Where the brief, the DAG or earlier work was wrong

The quarantine record reported a global-build failure but did not identify that the
current adopted source already marks `derivedPullback` irreducible. The restored Sheaf
file retained a now-invalid local irreducibility command copied from the earlier wrapper
version. Removing that redundant command makes the existing proof compile in 53.6 seconds
with the current WeilConjectures imports. The theorem statement and proof route remain
unchanged.

The preflight classified the local attribute edit as a CODEX change, so the required
change record is `coord/changes/DerivedPushforwardSquareMateUnit-irreducible-attribute.md`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
