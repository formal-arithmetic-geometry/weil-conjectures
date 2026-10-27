# CategoryTheory.BinaryPresentationModules and BinaryPresentationAdjointSquare

## Reason

The localized nerve proof needs the two comparison structures independently of the full
binary-cover presentation. Move their declarations verbatim to a small public data module
and publicly import it from the original module, avoiding an import cycle. This is a
location change only: every binder, universe, field and visibility stays unchanged.

## Old

```lean
structure BinaryPresentationModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R)) where
  modules : PresentationModules R ≌ PresentationModules S
  additive : modules.functor.Additive
  inverseAdditive : modules.inverse.Additive
  finiteLimits : PreservesFiniteLimits modules.functor
  finiteColimits : PreservesFiniteColimits modules.functor
  inverseFiniteLimits : PreservesFiniteLimits modules.inverse
  inverseFiniteColimits : PreservesFiniteColimits modules.inverse
  underlying : modules.functor ⋙ presentationForget S ≅ presentationForget R ⋙ g.inverse
  unit : modules.functor.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  structural : (presentationForget S).map unit.hom =
    underlying.hom.app (SheafOfModules.unit (localCoefficientRings R)) ≫ g.ringMap
  pushforward : modules.inverse ≅ g.modules
  derived : PresentationDerived R ≌ PresentationDerived S
  derivedFunctor : derived.functor =
    presentationDerivedMap modules.functor additive finiteLimits finiteColimits
  derivedInverse : derived.inverse = presentationDerivedMap modules.inverse inverseAdditive
    inverseFiniteLimits inverseFiniteColimits

/-- A restriction square preserves both adjunctions by their actual mates. Invertibility of
these mates says precisely that the adjoints are identified compatibly with units and counits,
rather than merely giving isomorphic endpoints.
Source: Stacks Categories, Tag 0B65; Sites, Tag 03EH
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationAdjointSquare
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') (F : A ⥤ B) (F' : A' ⥤ B') where
  comparison : F ⋙ E'.functor ≅ E.functor ⋙ F'
  rightMate : ∀ (G : B ⥤ A) (G' : B' ⥤ A') (a : F ⊣ G) (a' : F' ⊣ G'),
    IsIso ((mateEquiv a a' (TwoSquare.mk _ _ _ _ comparison.inv)).natTrans)
  leftMate : ∀ (L : B ⥤ A) (L' : B' ⥤ A') (a : L ⊣ F) (a' : L' ⊣ F'),
    IsIso (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ comparison.hom)).natTrans)

```

Declared in `Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation`.

## New

The exact declarations above are in
`Sheaf.CategoryTheory.Sites.BinaryPresentationModuleData`, publicly imported by
`Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation`. The original public imports
remain. No field or semantic change, including for the project's targets.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation | V5 | Publicly imports the data; all uses unchanged. |
| Sheaf.CategoryTheory.ToposOpenScalarUnit | unclaimed at inspection | Downstream importer; reexport preserves declarations and original API. No adaptation. |

`tools/downstream.py ... --uses CategoryTheory.BinaryPresentationModules` and the analogous
query for `CategoryTheory.BinaryPresentationAdjointSquare` both list only the item as a
textual user and ToposOpenScalarUnit as the single downstream module. The original
BinaryCoverSitePresentation structure and existence statement are unchanged.

## Status

landed 20261024T191518-L-416307 2026-10-24 (merge of deliver/V5/Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation)
