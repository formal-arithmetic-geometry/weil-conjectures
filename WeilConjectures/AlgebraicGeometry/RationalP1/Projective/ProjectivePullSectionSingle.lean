/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoIdSingleFunctor
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

-- The cached module-object instances keep elaboration from unfolding the coefficient rings.
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances in
/-- The canonical section comparison is the derived trivialization of the underived section
comparison, composed with the inverse of the derived factorization of the pullback. -/
private theorem pullSectionIso_eq_leftDerivedFunctorIdIso (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    pullSectionIso Λ Y f h =
      (Functor.leftDerivedFunctorFactorIso
        (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f)).symm ≪≫
      Functor.leftDerivedFunctorIdIso
        (CondensedRing.upperStarCongr Λ h ≪≫ CondensedRing.upperStarId Λ _) := by
  have hι : eqToIso (congrArg (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h) ≪≫
      CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y) =
      Functor.leftDerivedFunctorIdIso
        (CondensedRing.upperStarCongr Λ h ≪≫ CondensedRing.upperStarId Λ _) :=
    Functor.eqToIso_trans_leftDerivedFunctorIdIso
      (congrArg (fun g ↦ CondensedRing.upperStar Λ g) h) _ _ rfl _
  rw [pullSectionIso_eq, hι]
  rfl

/--
The single-complex component of the derived pullback section is the ordinary
section map conjugated by the two left-derived single comparisons.
-/
theorem projective_pull_section_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (pullSectionIso Λ Y f h).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) =
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor.map
        ((CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
          (CondensedRing.upperStar Λ f)).hom.app M) ≫
      (CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y))).hom.app
          ((CondensedRing.upperStar Λ f).obj M) ≫
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        (((CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
          CondensedRing.upperStarCongr Λ h ≪≫
          CondensedRing.upperStarId Λ (ProjectiveLine Y)).hom.app M) := by
  open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances in
  exact (congrArg (fun e ↦ e.hom.app
      ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M))
        (pullSectionIso_eq_leftDerivedFunctorIdIso Λ Y f h)).trans
    (Functor.leftDerivedFunctorFactorIso_symm_trans_idIso_hom_app_singleFunctor_obj
      (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f) _ M)

end AlgebraicGeometry.ProEtale.RationalP1
