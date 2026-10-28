/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module

public import Sheaf.Paper.LisseTowerPulledScalar
import Sheaf.Paper.LisseTowerFixedPullback
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition

/-! # Level comparisons for localized actual realizations

This is the level-comparison part of the actual localized realization argument.
Source: Stacks Project, Tags 03CY and 03DA.
(blueprint: lem-weil-pbc-lisse-tower-localized-actual-levels).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/-- Construct the actual comparison at every finite level after one more pro-etale
localization.  The construction pastes the canonical inverse-image comparison with
the supplied level comparison `e`; it uses no transition equation.
Source: Stacks Project, Tags 03CY and 03DA.
(blueprint: lem-weil-pbc-lisse-tower-localized-actual-levels).

Proof: identify fixed realization after inverse image with module inverse image after
fixed realization using the sheafification and inverse-image adjunctions.  Localize
that canonical comparison and paste the inverse-image compositors for `f.left`,
`V.hom`, and `U.hom` followed by `g`; the equality encoded by `f.w` identifies the
resulting scheme map with `W.hom`.  Apply the resulting comparison to `e n` for each
`n`.
-/
theorem lisseTower_localized_actual_levels
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    Nonempty (∀ (n : ℕ),
    (L n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  classical
  let a := f.left ≫ V.hom
  let b := U.hom ≫ g
  have hab : a ≫ b = W.hom ≫ g := by
    have hw := f.w
    change f.left ≫ (V.hom ≫ U.hom) = W.hom ≫ 𝟙 Y at hw
    erw [Category.comp_id] at hw
    simpa only [a, b, Category.assoc] using congrArg (fun t ↦ t ≫ g) hw
  refine ⟨fun n ↦ ?_⟩
  let B := lisseTowerEtaleRing d n
  let R := (pbcAdicRings X d).obj (op n)
  let RT := (adicTowerInverseImage b).obj R
  let RZ := (adicTowerInverseImage (a ≫ b)).obj R
  let c := (proEtaleRingInverseImageComp a b).symm.app R
  let P := proEtaleRingModulePullback a RT RZ c
  have hc : Iso.refl RZ = proEtaleRingCompositeCoefficients a b R RT RZ
      (Iso.refl RT) c := by
    apply Iso.ext
    change 𝟙 RZ = (proEtaleRingInverseImageComp a b).hom.app R ≫
      (adicTowerInverseImage a).map (𝟙 RT) ≫
        (proEtaleRingInverseImageComp a b).inv.app R
    erw [(adicTowerInverseImage a).map_id RT, Category.id_comp]
    exact (Iso.hom_inv_id_app (proEtaleRingInverseImageComp a b) R).symm
  let comp := (proEtaleCanonicalPullbackComposition_existsUnique a b R RT RZ
    (Iso.refl RT) c (Iso.refl RZ) hc).exists.choose
  let sq := (lisseTower_fixed_sheaf_pullback a b d n).some
  let dsq : (ProEtale.upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory ⋙
        lisseTowerFixedRealization (a ≫ b) d n ≅
      lisseTowerFixedRealization b d n ⋙ P.mapDerivedCategory :=
    Functor.isoWhiskerLeft _ (lisseTowerFixedRealizationIso (a ≫ b) d n).symm ≪≫
      Functor.mapDerivedCategorySquareIso sq ≪≫
      Functor.isoWhiskerRight (lisseTowerFixedRealizationIso b d n) P.mapDerivedCategory
  let starComp := Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp (ModuleCat.{u + 1} B) f.left V.hom) ≪≫
    Functor.mapDerivedCategoryCompIso
      (ProEtale.upperStar (ModuleCat.{u + 1} B) V.hom)
      (ProEtale.upperStar (ModuleCat.{u + 1} B) f.left)
  let C := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) U.left).mapDerivedCategory
  let K := C.obj (D n)
  have en : (lisseTowerFixedRealization b d n).obj K ≅
      (adicTowerPullback b R).obj (M.level n) := e n
  have result : (lisseTowerFixedRealization (a ≫ b) d n).obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K)) ≅
      (adicTowerPullback (a ≫ b) R).obj (M.level n) :=
    (lisseTowerFixedRealization (a ≫ b) d n).mapIso (starComp.symm.app K) ≪≫
      dsq.app K ≪≫ P.mapDerivedCategory.mapIso en ≪≫ (comp.app (M.level n)).symm
  rw [hab] at result
  exact result

end AlgebraicGeometry.Scheme
