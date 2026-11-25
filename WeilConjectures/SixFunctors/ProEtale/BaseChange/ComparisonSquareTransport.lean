/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization

/-! # Derived transport of a coherent comparison square

These statements use the defining expressions of the comparison isomorphisms of the smooth base
change file; they are the inputs of `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`.

## References

* [Stacks, Tag 0B65](https://stacks.math.columbia.edu/tag/0B65)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ComparisonCore

/-- Derived pullback comparisons transport an underived coherent square to the bounded-below
comparison square. -/
theorem comparison_square_of_component
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hcomp : ∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      ComparisonSquareComponent
        (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g
          { toCommSq := sq.toCommSq
            isoPullback := sq.isoPullback
            hom_fst := sq.isoPullback_hom_fst
            hom_snd := sq.isoPullback_hom_snd }) F) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
      (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) g' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f Λ).hom.app M) =
    (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) g Λ).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have he : comparisonSquareEtalePath Λ cs = comparisonSquareProEtalePath Λ cs :=
    comparisonSquarePaths_eq (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs) hcomp
  have hL := comparisonSquareEtalePath_normalization Λ sq M
  have hR := comparisonSquareProEtalePath_normalization Λ sq M
  have hd := congrFun (congrArg (comparisonSquareDerivedPath Λ g' f' f g) he) M
  exact eq_of_heq (HEq.trans (HEq.symm hL) (HEq.trans (heq_of_eq hd) hR))

end AlgebraicGeometry.ProEtale.ComparisonCore
