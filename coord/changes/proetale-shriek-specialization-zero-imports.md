# AlgebraicGeometry.Scheme.ProEt.shriek_sections_subsingleton_of_specializes_closed

## Reason

Prune the unused public dependency on the weakly-etale site-localization statement.
The theorem's signature and all public declarations are unchanged. The existing source
library imports already supply its small-site and Kan-extension definitions. The new proof
uses the source library's proved final-discrete indexing theorem instead of the module-valued
extension-by-zero interface. No definition or mathematical statement changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
```

All new proof imports are private. Other removed imports were private as well.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero --uses
shriek_sections_subsingleton_of_specializes_closed` reports sixteen downstream modules and
no use of this declaration outside its own module in the current source snapshot. The sole
direct importer already imports the removed public dependency independently.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero | D2 | Complete proof; public signature unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | Its own public import of ProEtaleWeaklyEtaleLocalization preserves the interface. No adaptation needed. |

The other fifteen transitive importers receive the removed dependency through this direct
importer, so no adaptation or target-statement review is needed. No other module is delivered.

## Status

landed 20261015T182201-L-784816 2026-10-15 (merge of deliver/D2/Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero)
