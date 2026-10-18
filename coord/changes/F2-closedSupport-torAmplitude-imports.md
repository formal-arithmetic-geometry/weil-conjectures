# AlgebraicGeometry.Etale.closedSupport_torAmplitude

## Reason

The completed proof only uses the supplied distinguished triangle, the bounded Tor
predicate from `Coefficients`, and the ordinary module-derived category vocabulary.
Remove three unused public imports from
`Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound`. This changes only the module's
re-exported imports. No declaration, definition, instance, attribute or theorem signature
changes. The remaining imports suffice to compile the original signature and the proof.
The five-step unit route and every declared proof dependency are retained.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound --uses AlgebraicGeometry.Etale.closedSupport_torAmplitude`
reported zero downstream modules, and only the item itself mentions the declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound | F2 | Proof completed; unused imports removed; signature unchanged. |

No consumer requires adaptation. No target statement or definition it uses changes.
The closed-support triangle remains an explicit hypothesis of this theorem; its existence
theorem is not used in this proof. The `def-kun-tor-amplitude` bounded predicate remains
used via `Coefficients`, so that node is not pruned.

## Status

landed 20261018T144405-L-3500487 2026-10-18 (merge of deliver/F2/Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound)
