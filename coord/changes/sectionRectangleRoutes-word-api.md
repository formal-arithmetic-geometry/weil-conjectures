# sectionRectangleLeft and sectionRectangleRight

## Reason

Present each independently specified section route as the same generic categorical
word used by the realization calculation. This retains exactly the original three
factors, in their original order, and avoids repeated kernel conversion of the
implicit derived-category instances of individual components. Every original
signature, hypothesis, attribute and visibility stays unchanged. No new data is
chosen and no target meaning changes. Kernel checking remains enabled and no
timeout is increased.

## Old

```lean
def sectionRectangleLeft (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedPullback Λ' c).obj
        ((s Y).pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) ⟶
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        ((s X').pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  (ModuleRingedComparison.derivedPullback Λ' c).map
      ((sectionRectangleRho φ f (s X) (s Y) (b f) (p f)).app
        ((ModuleRingedComparison.derivedFunctor Λ X).obj J)) ≫
    (sectionRectangleExchange Λ' sq).app
      ((s X).pair.derived.obj ((ModuleRingedComparison.derivedFunctor Λ X).obj J)) ≫
    (ModuleRingedComparison.derivedPushforward Λ' f').map
      ((sectionRectangleLambda φ a (s X') (s X) (b a) (p a)).hom.app
        ((ModuleRingedComparison.derivedFunctor Λ X).obj J))
```

```lean
def sectionRectangleRight (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedPullback Λ' c).obj
        ((s Y).pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) ⟶
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        ((s X').pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  (sectionRectangleLambda φ c (s C) (s Y) (b c) (p c)).hom.app
      ((ModuleRingedComparison.derivedPushforward Λ f).obj
        ((ModuleRingedComparison.derivedFunctor Λ X).obj J)) ≫
    (s C).pair.derived.map ((sectionRectangleExchange Λ sq).app
      ((ModuleRingedComparison.derivedFunctor Λ X).obj J)) ≫
    (sectionRectangleRho φ f' (s X') (s C) (b f') (p f')).app
      ((ModuleRingedComparison.derivedPullback Λ a).obj
        ((ModuleRingedComparison.derivedFunctor Λ X).obj J))
```

## New

```lean
def sectionRectangleLeft (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedPullback Λ' c).obj
        ((s Y).pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) ⟶
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        ((s X').pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  mateRouteLeft (ModuleRingedComparison.derivedPullback Λ' c)
    (sectionRectangleRho φ f (s X) (s Y) (b f) (p f))
    (sectionRectangleExchange Λ' sq)
    (sectionRectangleLambda φ a (s X') (s X) (b a) (p a)).hom
    ((ModuleRingedComparison.derivedFunctor Λ X).obj J)
```

```lean
def sectionRectangleRight (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedPullback Λ' c).obj
        ((s Y).pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) ⟶
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        ((s X').pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  mateRouteRight (s C).pair.derived
    (sectionRectangleLambda φ c (s C) (s Y) (b c) (p c)).hom
    (sectionRectangleExchange Λ sq)
    (sectionRectangleRho φ f' (s X') (s C) (b f') (p f'))
    ((ModuleRingedComparison.derivedFunctor Λ X).obj J)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | J6 | The own realization proof uses the exact same routes through generic word definitions. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Downstream importer; neither section route definition occurs. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Downstream importer; neither section route definition occurs. |

The read-only downstream.py --uses search confirms that only the item itself
mentions either route. All signatures remain unchanged, and no consumer adaptation
is necessary. The independent delivery reader checks the unchanged factors and
signatures.

## Status

landed 20261024T015051-L-2318376 2026-10-24 (merge of deliver/J6/Sheaf.Paper.ScalarGeometricExchangeRectangle)
