/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import all WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate

/-! # The canonical site comparison on Kummer-family cohomology
Source: det-prop-a1-kummer.proof.md, the etale/pro-etale comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

/-- The cohomology comparison is built from the actual direct-image counit mate,
with explicit total/Plus compatibility. It applies to all bounded-below complexes
and qcqs projections; no numerical cohomology computation is used.
Source: det-prop-a1-kummer.proof.md, site comparison in the geometric-fibre reduction
(blueprint: def-pur-kummer-site-cohomology-comparison).

Construction: exact inverse image commutes with homology. Apply homology to the
canonical direct-image mate, which is invertible for a qcqs projection and finite
coefficients. Pass from bounded-below to total right derivation, and then identify
exact comparison on the bounded-below complex with total exact comparison. Every
isomorphism is the specified functor comparison; no arbitrary comparison is chosen. -/
def kummerSiteCohomologyIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (n : ℤ) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f).obj F)) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj F.obj)) := by
  letI := isIso_fixedComparisonDirectImageMatePlus A f
  exact ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusHomologyFunctorIso
      n).app ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f).obj F) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ n).mapIso
      ((asIso (fixedComparisonDirectImageMatePlus A f)).app F) ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj F)) ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.app F))

private theorem sitePullback_inv_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (fixedComparisonPullbackPlus A f).inv =
      ((Functor.mapDerivedCategoryPlusCompIso
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
          (upperStar (ModuleCat.{u + 1} A) f)).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
        Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} A) f)
          (comparisonUpperStar (ModuleCat.{u + 1} A) X)).hom := by
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f
  let θ := (Functor.mapDerivedCategoryPlusCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (upperStar (ModuleCat.{u + 1} A) f)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
  have hσ : (Functor.mapDerivedCategoryPlusNatIso σ.symm).hom =
      (Functor.mapDerivedCategoryPlusNatIso σ).inv := by
    apply NatTrans.ext
    funext K
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.mapDerivedCategoryNatIso_symm]
    have h : DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusNatIso σ).app K) =
        (Functor.mapDerivedCategoryNatIso σ).app K.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app σ K)
    exact (congrArg Iso.inv h).symm
  have hθ : (fixedComparisonPullbackPlus A f).hom = θ.inv := by
    simp only [fixedComparisonPullbackPlus, θ, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, hσ, Category.assoc, σ]
  change (fixedComparisonPullbackPlus A f).inv = θ.hom
  apply (cancel_epi (fixedComparisonPullbackPlus A f).hom).1
  rw [Iso.hom_inv_id, hθ, θ.inv_hom_id]

/-- The specified site mate preserves the derived unit through the exact pullback
comparison. Source: det-prop-a1-kummer.proof.md, comparison of the degree-zero units
(blueprint: def-pur-kummer-site-cohomology-comparison).

Proof: the underived comparison is the mate of the inverse-image comparison.
The proved derived-mate factorization identifies its actual right-derived map with
the mate of the termwise derived comparison. Apply the mate-unit identity. No
cohomological calculation or invertibility of a scheme base-change map is used. -/
theorem kummerSiteComparison_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let C := ModuleCat.{u + 1} A
    let νY := comparisonUpperStar C Y
    νY.mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus C f).unit.app F) ≫
      (fixedComparisonDirectImageMatePlus A f).app
        ((Etale.upperStar C f).mapDerivedCategoryPlus.obj F) =
    (derivedUpperStarLowerStarAdjunctionPlus C f).unit.app
        (νY.mapDerivedCategoryPlus.obj F) ≫
      (lowerStar C f).rightDerivedFunctorPlus.map
        ((fixedComparisonPullbackPlus A f).inv.app F) := by
  dsimp only
  rw [sitePullback_inv_eq]
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  unfold fixedComparisonDirectImageMatePlus
  rw [underived_comparison_mate, derived_mate_eq]
  exact unit_mateEquiv
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus _ F

/-- Canonical site comparison commutes with taking the adjoint of an actual arrow.
Source: det-prop-a1-kummer.proof.md, comparison of the Kummer edge section
(blueprint: def-pur-kummer-site-cohomology-comparison).

Proof: write adjoint transposition as the unit followed by direct image. Naturality
of the specified direct-image mate moves the arrow past that mate. The proved unit
identity identifies the remaining composite with the pro-etale adjunction unit.
Functoriality recombines the target into its actual adjoint transpose. -/
theorem kummerSiteComparison_adjunct (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (c : (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj F ⟶ K) :
    let C := ModuleCat.{u + 1} A
    let νY := comparisonUpperStar C Y
    let νX := comparisonUpperStar C X
    νY.mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus C f).homEquiv _ _ c) ≫
      (fixedComparisonDirectImageMatePlus A f).app K =
    (derivedUpperStarLowerStarAdjunctionPlus C f).homEquiv _ _
      ((fixedComparisonPullbackPlus A f).inv.app F ≫ νX.mapDerivedCategoryPlus.map c) := by
  dsimp only
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (fixedComparisonDirectImageMatePlus A f).naturality c
  simp only [Functor.comp_map, Etale.rightDerivedLowerStarPlus] at hn
  simp only [Category.assoc]
  rw [hn, ← Category.assoc, kummerSiteComparison_unit]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale
