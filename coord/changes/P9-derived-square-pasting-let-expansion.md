# AlgebraicGeometry.Etale.derivedSquareIsoPasting

## Reason

Restore the quarantined module after the upstream sync. The quarantine entry
records a kernel deterministic timeout at original line 167. Profiling isolated
expensive definitional conversions involving the polymorphic local functions
`P`, `θ`, `c`, and `i`. Keeping these local functions caused deterministic
kernel timeouts or the 60-second file timeout, even after replacing the
original final rewrites with direct categorical cancellation.

Expand the local functions and coefficient alias in the statement, writing
`AddCommGrpCat.{u + 1}` explicitly throughout. This is exactly beta/zeta reduction of their original values;
`(upperStarCompDerivedPlus ...).symm.hom` is written `.inv`.
A token comparison after these explicit substitutions verifies that every
binder and every equation is otherwise identical. No hypothesis or conclusion
changes, and no definition, instance, attribute or public import changes.
The elaborated proposition is definitionally equal to the old proposition.
No target statement or definition changes; target semantic review is not reopened.

The final cancellation is proved in the existing private horizontal and
vertical comparison lemmas, using two fully proved generic cancellation
helpers. A private generic conjunction assembles these explicit formulas;
the public theorem specializes it to abelian groups. No new public API or
proof obligation is introduced.

## Old

```lean
theorem derivedSquareIsoPasting :
    let A := AddCommGrpCat.{u + 1}
    let P := fun {S T : Scheme.{u}} (q : S ⟶ T) => (upperStar A q).mapDerivedCategoryPlus
    let θ := fun {S T S' T' : Scheme.{u}} {a : S' ⟶ S} {b : S' ⟶ T'}
        {c : S ⟶ T} {d : T' ⟶ T} (sq : CommSq a b c d) => pullbackSquareComparison A sq
    let c := fun {R S T : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) =>
      (upperStarCompDerivedPlus A a b).symm
    let i := fun S : Scheme.{u} => upperStarIdDerivedPlus A S
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (θ (IsPullback.id_horiz f).toCommSq).hom.app K =
        (P f).map ((i Y).hom.app K) ≫ (i X).inv.app ((P f).obj K)) ∧
    (∀ {X Y X' Y' X'' Y'' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (P f'').map ((c h g).hom.app K) ≫
          (θ (sq₂.paste_horiz sq₁).toCommSq).hom.app K =
        (θ sq₂.toCommSq).hom.app ((P g).obj K) ≫
          (P h').map ((θ sq₁.toCommSq).hom.app K) ≫
          (c h' g').hom.app ((P f).obj K)) ∧
    (∀ {X Y X' Y' W W' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
        (sq₁ : IsPullback g' f' f g) (sq₃ : IsPullback g'' e' e g')
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (c e' f').hom.app ((P g).obj K) ≫
          (θ (sq₃.paste_vert sq₁).toCommSq).hom.app K =
        (P e').map ((θ sq₁.toCommSq).hom.app K) ≫
          (θ sq₃.toCommSq).hom.app ((P f).obj K) ≫
          (P g'').map ((c e f).hom.app K))
```

## New

```lean
theorem derivedSquareIsoPasting :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})),
      (pullbackSquareComparison AddCommGrpCat.{u + 1} (IsPullback.id_horiz f).toCommSq).hom.app K =
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.map
          ((upperStarIdDerivedPlus AddCommGrpCat.{u + 1} Y).hom.app K) ≫
          (upperStarIdDerivedPlus AddCommGrpCat.{u + 1} X).inv.app
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {X Y X' Y' X'' Y'' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})),
      (upperStar AddCommGrpCat.{u + 1} f'').mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h g).inv.app K) ≫
          (pullbackSquareComparison AddCommGrpCat.{u + 1}
            (sq₂.paste_horiz sq₁).toCommSq).hom.app K =
        (pullbackSquareComparison AddCommGrpCat.{u + 1} sq₂.toCommSq).hom.app
            ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj K) ≫
          (upperStar AddCommGrpCat.{u + 1} h').mapDerivedCategoryPlus.map
            ((pullbackSquareComparison AddCommGrpCat.{u + 1} sq₁.toCommSq).hom.app K) ≫
          (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h' g').inv.app
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {X Y X' Y' W W' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
        (sq₁ : IsPullback g' f' f g) (sq₃ : IsPullback g'' e' e g')
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})),
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e' f').inv.app
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj K) ≫
          (pullbackSquareComparison AddCommGrpCat.{u + 1}
            (sq₃.paste_vert sq₁).toCommSq).hom.app K =
        (upperStar AddCommGrpCat.{u + 1} e').mapDerivedCategoryPlus.map
            ((pullbackSquareComparison AddCommGrpCat.{u + 1} sq₁.toCommSq).hom.app K) ≫
          (pullbackSquareComparison AddCommGrpCat.{u + 1} sq₃.toCommSq).hom.app
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K) ≫
          (upperStar AddCommGrpCat.{u + 1} g'').mapDerivedCategoryPlus.map
            ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e f).inv.app K))
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting
--allow-missing --uses derivedSquareIsoPasting` finds no active importer or
textual user. Searches of both `lean/` and `quarantine/` find no other Lean
use of the theorem or import of this module. The module itself is currently
quarantined and held by P9. No other module requires adaptation. The DAG
attachment is updated to the expanded Lean signature; its mathematical
statement and its dependencies are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting | P9 | Restore with definitionally equal statement and complete proofs. |

## Status

landed 20261020T150700-L-2572860 2026-10-20 (merge of deliver/P9/Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting)
