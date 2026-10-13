module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! Unshifted coefficient identity used by the shifted scalar square.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-unshifted). -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

namespace RawModuleScalarComparison

noncomputable def derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f)

end RawModuleScalarComparison

/-- The derived scalar pullback comparison commutes with integer shifts.
Source: Stacks Project, Tags 03D7 and 03Q8. Expand the defining composite
into its three comparison isomorphisms and apply `NatTrans.shift_app_comm`
to each factor; compatibility of composition and associativity then give
the inverse composite's `CommShift` instance for every integer shift.
(blueprint: lem-sbc-raw-scalar-derived-pullback-shift) -/
theorem rawModuleScalar_derivedPullbackIso_commShift
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (RawModuleScalarComparison.derivedPullbackIso Λ f).inv ℤ := by
  sorry

/-- The unshifted coefficient-factor square follows by inverting the source-factor square
at the identity coefficient map and cancelling the derived scalar comparison.
Source: Stacks Project, Tags 03D7 and 03Q8. Specialize the source square to
the coefficient sheaf and identity map, use invertibility of its source
factors, and rewrite with `Functor.map_inv` and associativity. Cancellation
of the derived scalar comparison yields the displayed equality. This applies
to identity arrows, zero coefficients, and arbitrary schemes in the stated
universes.
(blueprint: lem-sbc-raw-scalar-coefficient-unshifted) -/
theorem rawModuleScalar_coefficient_unshifted
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A B : Over W) (f : A ⟶ B) :
    (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor
          0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G)) ≫
      ((RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)) =
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
      (((RawModuleScalarComparison.forget Λ B.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ B.hom G))) ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app _) := by
  sorry

end AlgebraicGeometry.Etale
