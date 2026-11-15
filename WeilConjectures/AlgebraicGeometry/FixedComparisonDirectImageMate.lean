/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonCounit

/-!
# Canonical direct-image mate in fixed coefficients

## Main definitions and statements

* `fixedComparisonPullbackPlus`: the canonical termwise pullback comparison.
* `fixedComparisonDirectImageMatePlus`: the canonical derived direct-image mate.
* `isIso_fixedComparisonDirectImageMatePlus`: its qcqs invertibility.
* `fixedComparisonDirectImageMatePlus_counit`: its specified counit normalization.

## References

* Stacks Project, Tags 099R and 0B65.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ProEtale

/-- The pullback comparison, induced termwise from the specified sheaf comparison.
Exact pro-etale pullback is its own left derived functor. (Stacks, Tags 099R and 0B65.) -/
noncomputable def fixedComparisonPullbackPlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)).symm ≪≫
  Functor.mapDerivedCategoryPlusNatIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
  Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)

/-- The canonical derived direct-image mate of the underived counit comparison.
(Stacks, Tags 099R and 0B65.) -/
noncomputable def fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))

/-- Invertibility of the specified mate for a qcqs morphism. (Stacks, Tag 099R.) -/
theorem isIso_fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (fixedComparisonDirectImageMatePlus Λ f) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)
  exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)))
    (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
      (ModuleCat.{u + 1} Λ) f I)

/-- The specified counit-mate normalization. It also characterizes the named component
as the adjoint transpose of the pulled-back etale counit after inverse pullback comparison.
(Stacks, Tag 0B65.) -/
theorem fixedComparisonDirectImageMatePlus_counit (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fixedComparisonPullbackPlus Λ f).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ f).app K) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f
  let θ := (Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
  have hb : fixedComparisonDirectImageMatePlus Λ f =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus θ.hom) := by
    unfold fixedComparisonDirectImageMatePlus
    rw [ComparisonCore.underived_comparison_mate,
      Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv]
  rw [hb, mateEquiv_counit]
  have hθ : (fixedComparisonPullbackPlus Λ f).hom = θ.inv := by
    have hσ : (Functor.mapDerivedCategoryPlusNatIso σ.symm).hom =
        (Functor.mapDerivedCategoryPlusNatIso σ).inv := by
      apply NatTrans.ext
      funext X
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.mapDerivedCategoryNatIso_symm]
      have h : DerivedCategory.Plus.ι.mapIso
          ((Functor.mapDerivedCategoryPlusNatIso σ).app X) =
          (Functor.mapDerivedCategoryNatIso σ).app X.obj :=
        Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app σ X)
      exact (congrArg Iso.inv h).symm
    simp only [fixedComparisonPullbackPlus, θ, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, hσ, Category.assoc, σ]
  rw [hθ]
  change θ.inv.app _ ≫ θ.hom.app _ ≫ _ = _
  rw [Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale
