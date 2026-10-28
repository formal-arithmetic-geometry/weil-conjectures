# Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoSections

## Reason

The item now assembles two smaller public proof statements: local transport through
the fixed realization and geometric descent to a derived Isom presheaf section. The
item module therefore needs the derived morphism comparison API and the two new
statement modules.

## Old

The item publicly imported
`Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom` and had no split modules.

## New

The item publicly imports
`Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison` and privately imports
`Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoDescent`. The delivery adds the public
modules `Sheaf.Paper.LisseFiniteLevelFixedRealizationLocalModel` and
`Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoDescent`, each exposing one strictly
smaller intermediate theorem used by the item proof.

## Users

The direct importer `Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms` was compiled
against the delivered modules and remains type correct. The new declarations are
available to the unfinished proof dependencies of this item.

## Status

Open delivery change; no existing declaration signature was altered.
