/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.HomologyBaseChange
public import WeilConjectures.TraceFormula.WeilSheafLowerStar

/-!

# Homology of the pushforward of Weil objects along a finite morphism

TODO

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Square

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Equal morphisms have equal derived pullbacks. -/
lemma leftDerivedUpperStar_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) :
    ((a)^*⟦Λ⟧).leftDerivedFunctor = ((b)^*⟦Λ⟧).leftDerivedFunctor := by
  rw [h]

/-- The comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of the derived pullbacks along a commutative
square `g' ≫ f = f' ≫ g`, built from the composition isomorphisms `leftDerivedUpperStarComp`. -/
noncomputable def leftDerivedUpperStarSquareIso (sq : CommSq g' f' f g) :
    ((g)^*⟦Λ⟧).leftDerivedFunctor ⋙ ((f')^*⟦Λ⟧).leftDerivedFunctor ≅
      ((f)^*⟦Λ⟧).leftDerivedFunctor ⋙ ((g')^*⟦Λ⟧).leftDerivedFunctor :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫ eqToIso (leftDerivedUpperStar_congr Λ sq.w.symm) ≪≫
    leftDerivedUpperStarComp Λ g' f

lemma leftDerivedUpperStarSquareIso_eq (sq : CommSq g' f' f g) :
    leftDerivedUpperStarSquareIso Λ sq = (leftDerivedUpperStarComp Λ f' g).symm ≪≫
      eqToIso (leftDerivedUpperStar_congr Λ sq.w.symm) ≪≫ leftDerivedUpperStarComp Λ g' f :=
  rfl

/-- The isomorphism of levelwise functors induced by the pullback comparison of module objects
is the square assembled from the composition isomorphisms. -/
lemma mapDerivedCategorySquareIso_upperStarSquareComparison (sq : CommSq g' f' f g) :
    Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq) =
      (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f' g)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (upperStar Λ) sq.w.symm)) ≪≫
        Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ g' f) := by
  rw [upperStarSquareComparison_eq]
  refine Iso.ext ?_
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rfl

/-- **The derived pullback comparison is the levelwise one**: through the identifications of the
derived pullbacks with the levelwise pullbacks, `leftDerivedUpperStarSquareIso` is the
isomorphism induced by the pullback comparison of module objects. -/
lemma leftDerivedUpperStarSquareIso_hom_app_eq (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (f')^*⟦Λ⟧.mapDerivedCategory.map ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f').inv.app
          (((g)^*⟦Λ⟧).leftDerivedFunctor.obj K) ≫ (leftDerivedUpperStarSquareIso Λ sq).hom.app K =
      (Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq)).hom.app K ≫
        (g')^*⟦Λ⟧.mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ g').inv.app
          (((f)^*⟦Λ⟧).leftDerivedFunctor.obj K) := by
  have h :=
    Iso.squareComparison_hom_app_eq (leftDerivedUpperStarIsoMapDerivedCategory Λ g)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f') (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g')
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (f' ≫ g))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (g' ≫ f))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f' g))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ g' f)) _ _
    (leftDerivedUpperStarComp_hom_app_eq Λ f' g) (leftDerivedUpperStarComp_hom_app_eq Λ g' f)
    (leftDerivedUpperStar_congr Λ sq.w.symm)
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (upperStar Λ) sq.w.symm)))
    (leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_eqToHom Λ sq.w.symm)
    _ (mapDerivedCategorySquareIso_upperStarSquareComparison Λ sq) K
  rw [leftDerivedUpperStarSquareIso_eq]
  with_reducible exact h

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
