## What changed

The assigned theorem `AlgebraicGeometry.Scheme.lisseTower_localized_constants` is now a
complete assembly proof. It obtains the family of constant model isomorphisms from
`lisseTower_localized_constants_model` and obtains the normalized semilinear equation
from `lisseTower_localized_constants_normalization`, then packages them after unfolding
the local functor.

Added the private proof imports and modules
`Sheaf.Paper.LisseTowerLocalizedConstantsModel` and
`Sheaf.Paper.LisseTowerLocalizedConstantsNormalization`. Their statements isolate,
respectively, model existence and the normalized transition equation for a supplied
model family. No existing definition, public statement, or source-library module was
changed.

All three modules compile together with `lcompile.py --all` without warnings. The
original theorem signature is unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.lisseTower_localized_constants` by a complete Lean proof.

Added two strictly smaller holes:

- `AlgebraicGeometry.Scheme.lisseTower_localized_constants_model`, node
  `lem-weil-pbc-lisse-tower-localized-constants-model`;
- `AlgebraicGeometry.Scheme.lisseTower_localized_constants_normalization`, node
  `lem-weil-pbc-lisse-tower-localized-constants-normalization`.

The first only constructs the family of model isomorphisms. The second assumes such a
family and proves only its normalized transition equation. Neither theorem repeats the
full target conclusion. The delivery therefore decomposes one upper obligation into two
strictly smaller source-level obligations; no `sorry` remains in the assigned module.

## No longer needed

No original import is removed and no existing module is withdrawn. The original planned
proof dependencies are retained through the two split statements; the item itself uses
only those two new modules directly. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The target's two long proof steps are independent mathematical obligations, but the
available library has no single declaration supplying either the normalized model family
or its semilinear transition equation. Treating them as one proof leaves no usable
intermediate interface. The DAG route is therefore recorded as two genuine lower-level
nodes followed by an explicit assembly proof. No statement is disputed, and no target
signature or definition was changed.

## New nodes

`lem-weil-pbc-lisse-tower-localized-constants-model` records the constant model family
before any semilinear transition is considered.

`lem-weil-pbc-lisse-tower-localized-constants-normalization` records the normalized
semilinear transition equation for an arbitrary supplied model family.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerLocalizedConstants": "af59fb5c01eecc20d186fdb899372f95a204c5e9", "Sheaf.Paper.LisseTowerLocalizedConstantsModel": "58e4f16d2b375560e4fbbb0af7060c9e3330ff6a", "Sheaf.Paper.LisseTowerLocalizedConstantsNormalization": "c73ef850cac4de7e78844c511acd417ea0718377"}, "results": {}, "time": "2026-10-28T07:57:42+0800", "transitive": 0, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
