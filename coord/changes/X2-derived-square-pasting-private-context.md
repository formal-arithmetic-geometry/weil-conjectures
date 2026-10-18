# AlgebraicGeometry.Etale.derivedSquareIsoPasting

## Reason

The proof adds a scoped coefficient variable context for six fully proved private
lemmas. The delivery classifier conservatively regards the additional section/variable
commands as an interface change and requires this record. The context ends before the
existing public theorem, whose signature below is identical before and after.
No declaration, definition, instance, notation, or public import changes its meaning.
All helpers are private, including the generated reassociated versions.
No target statement or definition changes; semantic target review is not reopened.

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

The same public signature, with its proof completed:

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

The new generic context, confined to the private-helper section, is:

```lean
section

variable (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

-- Fully proved private lemmas only.

end
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting --uses
 derivedSquareIsoPasting` finds only the declaring module as a textual user of this
name. Its 393 transitive importers all receive the same public declarations, with
identical types and public imports. None requires adaptation; none is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting | X2 | Scoped private context; existing public theorem proved with identical signature. |

## Status

landed 20261018T062945-L-690351 2026-10-18 (merge of deliver/X2/Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting)
