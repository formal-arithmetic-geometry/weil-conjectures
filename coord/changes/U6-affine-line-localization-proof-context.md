# AlgebraicGeometry.ProEtale.RationalP1.rationalP1_adjunction_assembly

## Reason

Keep the standard derived-category localization constructors folded during elaboration
of the private localization package and the diagonal assembly. These are local
reducibility attributes; the existing theorem signature, definitions and public imports
are unchanged. The new localization construction is private and contains no sorry.
The interface checker conservatively records changes to top-level attribute commands.
The additional universe names `v₁` through `v₅` are used only by the proved private
logical helper `selectNormalizedArrow`; the assembly theorem still has exactly its
original universe parameter u and signature.
No target changes meaning and no consumer adaptation is needed.

## Old

The original universe declaration was `universe u`.
The existing local reducibility command, verbatim:

```lean
attribute [local irreducible] push exceptional coefficient line
```

## New

The new universe declaration is `universe u v₁ v₂ v₃ v₄ v₅`.
The local reducibility commands, verbatim:

```lean
attribute [local irreducible] push exceptional coefficient line

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
```

The added `diagonalLocalizations` definition is private and marked
`@[irreducible]`. It packages the seven existing localization and Ext structures
using their standard Grothendieck constructions. Its irreducibility keeps the chosen
localization data folded during downstream matching; it introduces no alternative module
category, arbitrary mathematical witness or public instance.

## Users

`tools/downstream.py Sheaf.Paper.AffineLineAdjunctionAssembly --uses
rationalP1_adjunction_assembly` reports the item and the caller below. This caller is
also the sole direct importer. Other transitive importers see the same theorem and
public imports. Local reducibility attributes do not propagate through imports.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineLineAdjunctionAssembly | U6 | Private localization construction and completed proof. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same adjunction theorem and public imports; no adaptation. |

## Status

landed 20261026T071239-L-3905477 2026-10-26 (merge of deliver/U6/Sheaf.Paper.AffineLineAdjunctionAssembly)
