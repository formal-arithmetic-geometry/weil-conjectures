# AlgebraicGeometry.Etale.relativeHigherDirectImageExchange

## Reason

The item now reduces continuity to local descent and eventual zero detection of
raw derived classes. These supporting statements need the actual exchange map.
Keeping its construction in the theorem module would make their imports cyclic.
Move the existing definition, verbatim, into a construction module and publicly
re-export it from its original module. Its name, universe, signature, visibility,
attributes and body are preserved. No upstream source-library file is edited.

The new derived coefficient/exchange map is also a real construction from the
existing derived mate, exact inverse-image/single comparison and coefficient
morphism. No data are selected from an existence theorem. The canonical
free-sheaf derived-section comparison receives an irreducible construction with
a proved local-bijectivity and naturality API. It uses the existing public
AbelianComparison constructions; their private local-bijectivity theorem is
used only inside a theorem proof. This avoids repeated unfolding of free-sheaf
and derived Hom group structures in its consumers. Local irreducibility
attributes prevent elaboration from expanding the existing inverse-image
constructions. No source declaration or source attribute is changed. The raw-section functor
is concretely shift followed by additive Yoneda and precomposition by the free
sheaf/single functor. Its objects and maps are irreducible to prevent repeated
conversion of expanded derived Hom groups in point fibres. A separately named
irreducible exact-pullback homology isomorphism exposes the original exchange
through a proved equation. These are representation APIs with explicit bodies,
not new choices or continuity assumptions.

## Old

In lean/Sheaf/AlgebraicGeometry/RelativeHigherDirectImageContinuity.lean:

```lean
noncomputable def relativeHigherDirectImageExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} g').obj F ⟶ F') (q : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F')) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) ≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusSingleFunctor
            0).hom.app F ≫
            (DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map φ))
```

## New

In lean/Sheaf/AlgebraicGeometry/RelativeHigherDirectImageExchange.lean:

```lean
noncomputable def relativeHigherDirectImageExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} g').obj F ⟶ F') (q : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F')) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) ≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusSingleFunctor
            0).hom.app F ≫
            (DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map φ))

/-- Exact inverse image commutes with homology of a derived direct image.
This names the concrete comparison to keep its construction out of consumers.
Source: Stacks Project, Tag 07A7.
(blueprint: def-kun-relative-higher-image-homology-iso). -/
@[irreducible]
noncomputable def relativeHigherDirectImageHomologyIso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≅
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).app _

/-- The degreewise comparison is homology of the derived coefficient mate,
preceded by the exact-pullback homology comparison.
Source: Stacks Project, Tags 07A7 and 0EYM.
(blueprint: lem-kun-relative-higher-image-exchange-homology).

Proof: Both constructions are the same composite by their explicit definitions.
This equation is the unfolding API; consumers need not unfold either mate. -/
theorem relativeHigherDirectImageExchange_eq_homology
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} g').obj F ⟶ F') (q : ℕ) :
    relativeHigherDirectImageExchange sq F F' φ q =
      (relativeHigherDirectImageHomologyIso f g F q).hom ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
        (relativeHigherDirectImageDerivedMap sq F F' φ) := by
  unfold relativeHigherDirectImageHomologyIso
  rfl
```

The original module publicly imports the new construction module. Its theorem
signature is byte-for-byte unchanged. The new module preserves all seven old
public imports, and the original module preserves the other six old public
import lines, so every original public dependency remains visible. The new
construction and comparison declarations are under Sheaf/.

## Users

The returned delivery at 78f937a7247 omitted two current users of
AlgebraicGeometry.Etale.relativeHigherDirectImageExchange. The current source
search finds HigherDirectImagesLimits and RelativeHigherImageContinuityPreorder,
as well as the item. Both existing consumers are unclaimed in coord/claims.
RelativeHigherImageContinuityPreorder publicly imports the original module and
uses the exchange in its relativeHigherImageExchange abbreviation.
HigherDirectImagesLimits uses that abbreviation and unfolds the exchange in
relativeExchange_eq. The public re-export preserves the exchange's original
name, signature, attributes and body, so neither consumer requires a source edit.
The read-only downstream.py scan now reports nine downstream modules and exactly
these three textual users of the declaration (including the item). Both
consumers are included in the table below and checked against this delivery.

DAG parents lem-kun-0ezt and lem-pur-relative-support-coordinate-model still cite
the item and are retained. Neither parent needs adaptation because the same
theorem and exchange construction remain available from the same public import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImagesLimits | unclaimed | Uses and unfolds the verbatim exchange via relativeHigherImageExchange; public re-export preserves its proof unchanged. |
| Sheaf.AlgebraicGeometry.RelativeHigherImageContinuityPreorder | unclaimed | Publicly imports the item; its exchange abbreviation and continuity proof retain the same declarations and mathematical meaning. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity | H5 | Public re-export of verbatim exchange construction; theorem signature preserved. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange | H5; new | Houses the old exchange construction and the new derived coefficient map. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageRawLocalDescent | H5; new | Uses the actual derived exchange with coefficient coprojection. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageFiniteRawVanishing | H5; new | Proves finite-stage zero detection and common-index assembly. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageCohomologyKernel | H5; new | Raw cohomological kernel in the higher-image sheaf colimit. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageGermDescent | H5; new | Uses exact pullback homology to identify the actual higher-image leg. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageAffineSectionVanishing | H5; new | Uses the same leg identification before the two local refinements. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageGermVanishing | H5; new | Depends on affine section vanishing. |
| Sheaf.AlgebraicGeometry.DerivedHomologySectionsComparison | H5; new | Concrete canonical comparison and its proved API. |

No target or definition used by a target changes mathematical meaning: the old
exchange construction is literally the same expression. No definition repair,
weakening, withdrawal, or forced adaptation of another holder's work occurs.

## Status

landed 20261020T233151-L-901470 2026-10-20 (merge of deliver/H5/Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity)
