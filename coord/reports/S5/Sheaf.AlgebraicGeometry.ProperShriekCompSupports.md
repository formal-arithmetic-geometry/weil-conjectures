## What changed

Added `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw`, which isolates the canonical-composite compactification calculation as a named intermediate theorem. The assigned module now proves the equality-congruence expansion of `properRouteCompIso` through a private helper; its original compositor theorem remains connected to the raw intermediate theorem for subsequent completion.

## Proved and sorry left

Proved the private helper `properRouteCompIso_inv_app_eq`, which expands the inverse of `properRouteCompIso` into the inverse canonical compositor followed by the equality congruence. The assigned declaration `AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports` remains a sorry. The new declaration `AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports_raw` also remains a sorry, with node `lem-sf-proper-shriek-compositor-supports-raw`. No definition contains a sorry.

## No longer needed

No planned proof dependency was removed. The raw theorem imports only `Sheaf.AlgebraicGeometry.ProperSupportedKunnethRoute` and `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`, matching the compactification interfaces used by the split calculation.

## Where the brief, the DAG or earlier work was wrong

The original node combines equality transport, compactification refinement transport, open/proper exchange, and ordinary compositor associativity. The equality transport is a separate definitional substep, while the remaining canonical-composite calculation is strictly smaller and has been recorded as a new node. The exact raw calculation still requires the compactification proof described in its docstring and DAG steps.

## New nodes

`lem-sf-proper-shriek-compositor-supports-raw` records the canonical-composite compactification calculation in `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw`.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
