# AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization

## Reason

Restore the quarantined zero-hole module after the upstream sync. Its proof called
`Etale.pullbackSquareComparison_def`, which is no longer provided by the source library.
Direct unfolding repairs that call, but the old final proof then reaches a deterministic
kernel timeout: it compares the original commutative square to the projection of a
reconstructed `ChosenCartesianSquare` inside the concrete comparison component.
The repaired private restriction identity takes `CommSq` directly. A fully proved
private helper combines the path equations for a variable component, then the public
proof specializes it and the restriction identity at the identical `sq.toCommSq`.
The complete module compiled in 7.8 seconds before final cleanup, within the unchanged
60-second limit. No upstream module, public definition, public import, option, attribute,
or mathematical statement is changed.

## Old

The archived exported signature is:

```lean
theorem comparisonSquareEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
          (leftDerivedUpperStarComparisonIso g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((leftDerivedUpperStarComparisonIso f Λ).hom.app M))
```

The private `plus_square_expansion` and `square_restrict` helpers accepted
`ChosenCartesianSquare`; the former used the removed `_def` lemma. The final theorem
combined the concrete square restriction and edge equations directly.

## New

The exported signature stays verbatim:

```lean
theorem comparisonSquareEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
          (leftDerivedUpperStarComparisonIso g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((leftDerivedUpperStarComparisonIso f Λ).hom.app M))
```

`plus_square_expansion` now unfolds the original definition and accepts `CommSq`.
`square_restrict` also accepts `CommSq` and retains the explicitly expanded ordinary
comparison in its conclusion. The proved private `normalization_aux` combines that
restriction equation with the existing pasting and edge identities for a component
variable. The final proof specializes it to the actual component. The now-unused
private `etale_square_expansion` helper is removed. No public interface is altered.

## Users

The live downstream tool reports the quarantined item as an unknown module. A search
of both `lean/` and `quarantine/` finds only `ComparisonSquareTransport` importing the
item or calling its theorem. The other four consumers below are additionally named
in `coord/rework.tsv` as quarantined dependents. No consumer source needs adaptation:
the exported signature, definitions, and import visibility are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization | G3 | Restored; private proof repair only. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | unclaimed in local claim snapshot | Unchanged archived consumer compiled in 6.6 seconds against the repair; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed in local claim snapshot | Unchanged statement and dependencies; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportProperFactor | unclaimed in local claim snapshot | Unchanged interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen | unclaimed in local claim snapshot | Unchanged interface and meaning; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local claim snapshot | Unchanged interface and meaning; no adaptation. |

## Status

landed 20261020T145512-L-2403791 2026-10-20 (merge of deliver/G3/Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization)
