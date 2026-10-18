# AlgebraicGeometry.Etale.derivedExtensionZeroBaseChange proof setup

## Reason

The preflight conservatively reports changes to module commands when private helper sections
introduce scoped variables, an `open`, or local instances. This record documents those commands.
There is no changed public signature, public definition, public import, global instance, notation,
or attribute. The existing theorem receives a proof; private helpers provide its glue.
All three existing public signatures and both public definition bodies were compared verbatim.
No consumer requires adaptation.

## Old

The original setup, verbatim (with the two definitions between the variable and theorem), is:

```lean
universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
```

No old public signature or definition is replaced. The original theorem ended `:= by sorry`.

## New

The original setup remains. Before the original coefficient variable, add a private-helper
section whose setup, verbatim, is:

```lean
section DerivedTools

open CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
```

Every declaration in that section is a proved `private theorem`; the section closes with
`end DerivedTools`, so its open namespace, local instances and variables do not escape.
The next private-helper section has this setup, verbatim:

```lean
section Underived

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
```

Every declaration in it is again a proved `private theorem`; it closes with `end Underived`.
Two `omit [HasSmallSiteSheafify A] in` commands avoid unused section assumptions for private
helpers. Options `backward.isDefEq.respectTransparency` and
`backward.defeqAttrib.useBackward` are set with `in` on individual declarations only.
Their exact positions and scopes are visible in the delivered source. No global option changes.
The original coefficient variable, public signatures and public definitions remain verbatim.

## Users

`tools/downstream.py` reports six direct importers and 406 transitive importers. Its `--uses`
check finds the public exchange/composition definitions in `ProperOpenComparison` and
`ProperOpenInterchangeCoherence`; the public theorem has no textual consumer yet. Each affected
public declaration remains verbatim in signature, and each definition remains verbatim in body.
The command changes are scoped to private proof sections. Therefore all 406 transitive importers
have identical APIs and elaboration instances available from this module. No target meaning
changes, and no other module is adapted. The table lists the own module and every direct importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange | E3 | Own module: proved private helpers and original theorem; public API unchanged. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | B2 | No effect: scoped setup does not escape; every public signature and definition is identical. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | B9 | No effect: scoped setup does not escape; every public signature and definition is identical. |
| Sheaf.AlgebraicGeometry.ProperOpenComparison | F1 | No effect: scoped setup does not escape; every public signature and definition is identical. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | F2 | No effect: scoped setup does not escape; every public signature and definition is identical. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | F3 | No effect: scoped setup does not escape; every public signature and definition is identical. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | F4 | No effect: scoped setup does not escape; every public signature and definition is identical. |

## Status

landed 20261018T062733-L-643101 2026-10-18 (merge of deliver/E3/Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange)
