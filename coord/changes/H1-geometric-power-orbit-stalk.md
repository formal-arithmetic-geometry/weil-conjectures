# AlgebraicGeometry.WeilSheaf.exists_stalk_equiv_of_power_orbit

## Reason

Separate the scheme-theoretic deck-point construction from local stalk naturality, while
proving commutation of iterated returns and restriction to monic subobjects in Lean.

## Old

No public declarations existed at the three new module paths. The existing item declared
`AlgebraicGeometry.WeilSheaf.exists_stalk_equiv_of_power_orbit` with proof `by sorry`.

## New

The existing theorem's signature and visibility are unchanged. It now has a complete proof
from two independent intermediate statements and proved categorical commutation/cancellation.

New additive API only:

- `Sheaf.DeligneLaumon.FrobeniusPowerCommutation`: explicit iteration comparisons,
  `frobeniusPowerCommIso`, and the proved `frobeniusPowIso_comm`.
- `Sheaf.DeligneLaumon.FrobeniusPowerDeckPoints`: the explicitly composed
  `frobeniusPowerTranslatePoint` and `exists_frobenius_power_deck_point`.
- `Sheaf.DeligneLaumon.FrobeniusPowerStalkTransport`:
  `nonempty_stalk_equiv_of_equivariant_power_translate`.

Each module has its attached node with the exact theorem statement and proof in words.
No existing definition, declaration signature, instance, attribute or public import changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.GeometricPowerOrbitStalk | H1 | uses all three new modules in its proof |
| Sheaf.DeligneLaumon.FrobeniusPowerStalkTransport | new in this delivery | uses comparison definitions |

These are all users of the new APIs. Existing consumers of the item see its unchanged public
interface. No forced consumer adaptations are necessary.

## Status

landed 20261026T065845-L-3269080 2026-10-26 (merge of deliver/H1/Sheaf.DeligneLaumon.GeometricPowerOrbitStalk)
