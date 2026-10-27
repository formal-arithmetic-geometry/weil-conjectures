## What changed

Change record: `coord/changes/z7-henselian-residual-proof-support.md`. The first preflight requested a record for added module commands; affine helper instances and private irreducibility attributes are now local.

Proved `AlgebraicGeometry.Scheme.HenselianPointedResidualCover.henselian_pointed_residual_cover_lift` without changing its statement or the public definitions. All constructions are explicit: global-section stage rings and colimit, the pointed equivalence, canonical quotient pullback comparisons, and the unique isomorphism of residual limit cones. Private helpers prove the required algebra and comparison identities. The complete module compiled without warnings through `lcompile.py` (52.3 seconds with the final local attributes).

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Scheme.HenselianPointedResidualCover.henselian_pointed_residual_cover_lift` (node `lem-sfb-henselian-pointed-residual-cover-lift`). Added zero holes and zero split statements. No `sorry` remains in the item module.

## No longer needed

Removed unused proof imports `Mathlib.Algebra.Category.CommAlgCat.Basic` and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; the proof works directly in `Under E` and does not need quasi-separatedness.

Removed the obsolete `lem-weil-pbc-ind-etale-stability` entry from `tool_uses`. Removed the proof import `Sheaf.RingTheory.IndEtaleStability` and the proof dependency `lem-weil-pbc-ind-etale-stability`: the Mathlib ind-closure composition API and the stage colimit presentation suffice. The normal-subgroup comparison theorem `lem-sfb-pointed-galois-limit-geometry` is unnecessary for this proof: the prescribed `UniversalCover.Index` is already a small cofiltered category. No library module is withdrawn. Removed `lem-sfb-pointed-finite-etale-limit-cover` from proof dependencies (its statement dependency and public import stay); its coordinate existence theorem `UniversalCover.nonempty_pointedLimitCechCoordinates` is not used: the required basic geometry is already proved in `UniversalCoverConstruction`.

## Where the brief, the DAG or earlier work was wrong

The Jacobson radical assertion is already a field of the existing `HenselianRing` API. The zero-ideal conclusion follows directly from the canonical residual quotient bijection; it does not require reconstructing a second colimit. No statement repair or unit-route change was needed.

Launcher metadata note: the resumed sandbox reference start is now 1792773804.131394;
the original dispatched attempt began at 1792750307.711223. The launcher paused and
resumed the session to reduce the compile queue; no worker changed `.budget`.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
