# Shared finite local freeness under coefficient isomorphisms

## Reason

The landing check returned the delivery because two new E3 modules proved the identical
private helper `finiteLocallyFree_restrict`. Keep the normalization module's existing proof,
expose it for reuse, and remove the duplicate proof and its unused `coefficientUnitIso` helper
from pair transport. The new pair-transport import is proof-only. Both modules are new in
this delivery, not modules held by another group. No target or existing library signature
changes, and no definition changes meaning.

## Old

In `lean/Sheaf/AlgebraicGeometry/LisseLatticeCoefficientNormalization.lean`, and identically
in `lean/Sheaf/AlgebraicGeometry/IntegralLatticeCoefficientTransport.lean`:

```lean
private theorem finiteLocallyFree_restrict {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u + 1}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J RingCat.{u + 1}) (e : S ≅ R)
    (L : SheafOfModules.{u + 1} R) [h : L.IsFiniteLocallyFree] :
    ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj L).IsFiniteLocallyFree
```

## New

The normalization module keeps its original proof and exposes the theorem:

```lean
theorem finiteLocallyFree_restrict {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u + 1}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J RingCat.{u + 1}) (e : S ≅ R)
    (L : SheafOfModules.{u + 1} R) [h : L.IsFiniteLocallyFree] :
    ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj L).IsFiniteLocallyFree
```

Pair transport has no copy of this declaration and imports normalization using a plain
`import`. Its application of `finiteLocallyFree_restrict` now resolves to the shared public
proof. The normalization node records both public declarations, and the pair-transport node
records the normalization proof dependency.

## Users

All affected modules are new E3 modules retained in the returned sandbox. Searching the
current shared repository finds no existing declaration or consumer of this helper.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization` | E3 (new) | Exposes its existing helper; its normalization proof is unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport` | E3 (new) | Imports and applies the shared helper; removes the duplicate and unused unit isomorphism. |
| `Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport` | E3 (new) | Its pair-transport dependency now reuses normalization; source unchanged. |
| `Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf` | E3 (new) | Its two proof paths share one finite local freeness theorem; source unchanged. |
| `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal` | E3 | Final theorem signature and proof unchanged by this repair. |

## Status

landed 20261016T070240-L-770593 2026-10-16 (merge of deliver/E3/Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal)
