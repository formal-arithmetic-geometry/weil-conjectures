/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate


/-! # Augmentation coherence for completed pullback

This is the strict derived-category square needed by the direct-image completion
unit.  Its proof is the localization calculation comparing the normalized cone
map with the degree-zero cone inclusion.
(blueprint: aux-weil-pbc-direct-image-augmentation-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical pullback/reduction comparison carries the degree-zero
augmentation through constant towers.  This is obtained by expanding
`Localization.liftNatTrans` and applying the inr equation for mapping cones;
the normalization equation `IsPullReduction` then identifies the two localized
maps.  It is independent of any choice of K-injective representative.
(blueprint: aux-weil-pbc-direct-image-augmentation-coherence) -/
theorem directImage_augmentation_pullReduction_coherence :
    ∀ M : DerivedCategory (AdicCompletion.Modules l E Y),
      (dpull l E f).map ((augmentation l E Y).app M) ≫
          (pullReduction l E f).hom.app M =
        (constantInterchange l E
          (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv.app M ≫
          (augmentation l E X).app ((dpullModule l E f).obj M) := by
  let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let α : dconstant l E Y ⋙ dpull l E f ⟶
      dpullModule l E f ⋙ red l E X :=
    Functor.whiskerRight (augmentation l E Y) (dpull l E f) ≫
      (pullReduction l E f).hom
  let β : dconstant l E Y ⋙ dpull l E f ⟶
      dpullModule l E f ⋙ red l E X :=
    (constantInterchange l E H).inv ≫
      Functor.whiskerLeft (dpullModule l E f) (augmentation l E X)
  have hab : α = β := by
    have hinr (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
        ((pull l E f).mapHomologicalComplex (.up ℤ)).map
              (CochainComplex.mappingCone.inr ((complexPowerMap l E Y).app P)) ≫
            (strictPullReduction l E f).hom.app P =
          (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P ≫
            CochainComplex.mappingCone.inr ((complexPowerMap l E X).app
              ((H.mapHomologicalComplex (.up ℤ)).obj P)) := by
      apply HomologicalComplex.Hom.ext
      funext i
      apply NatTrans.ext
      funext n
      exact (strictPullReduction_existsUnique l E f).exists.choose_spec P i n.unop |>.2
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ))
    intro P
    dsimp only [α, β, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    dsimp only [augmentation]
    simp only [Localization.liftNatTrans_app, Localization.Lifting.iso]
    apply (cancel_mono ((red l E X).map
      (H.mapDerivedCategoryFactors.hom.app P) ≫
      (redFactors l E X).hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj P))).1
    let cY := (constant l E Y).mapDerivedCategoryFactors.hom.app P
    let inrY : ((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P ⟶
        (strictRed l E Y).obj P := by
      exact CochainComplex.mappingCone.inr ((complexPowerMap l E Y).app P)
    let iY : DerivedCategory.Q.obj
          (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        DerivedCategory.Q.obj ((strictRed l E Y).obj P) := by
      exact DerivedCategory.Q.map
        inrY
    let inrX : ((constant l E X).mapHomologicalComplex (.up ℤ)).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        (strictRed l E X).obj ((H.mapHomologicalComplex (.up ℤ)).obj P) := by
      exact (strictAugmentation l E X).app
        ((H.mapHomologicalComplex (.up ℤ)).obj P)
    have hforward :
        (constantInterchange l E H).hom.app (DerivedCategory.Q.obj P) ≫
            (pull l E f).mapDerivedCategory.map cY ≫
            (pull l E f).mapDerivedCategoryFactors.hom.app
              (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) =
          (dconstant l E X).map
              (H.mapDerivedCategoryFactors.hom.app P) ≫
            (constant l E X).mapDerivedCategoryFactors.hom.app
              ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).hom.app P) := by
      have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors H
        (constant l E X) P
      have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors
        (constant l E Y) (pull l E f) P
      dsimp [constantInterchange]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      rw [hG, Functor.mapDerivedCategoryNatIso_fac, ← hF]
      simp only [Iso.hom_inv_id_app_assoc, Category.assoc]
      simp only [NatIso.mapHomologicalComplex]
    have hbetaSimpl :
        (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫
            (augmentation l E X).app
              ((dpullModule l E f).obj (DerivedCategory.Q.obj P)) ≫
            (red l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
            (redFactors l E X).hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
          (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫
            (dconstant l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
            (constant l E X).mapDerivedCategoryFactors.hom.app
              ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map inrX := by
      have hnat := (augmentation l E X).naturality
        (H.mapDerivedCategoryFactors.hom.app P)
      rw [← reassoc_of% hnat]
      dsimp [augmentation, inrX]
      simp only [Localization.liftNatTrans_app, Localization.Lifting.iso,
        Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
        Category.comp_id,
        Functor.whiskerRight_app]
    have hpr := (pullReduction_existsUnique l E f).exists.choose_spec P
    have hpr' :
        (dpull l E f).map cY ≫ (dpull l E f).map iY ≫
            ((dpull l E f).map ((redFactors l E Y).inv.app P) ≫
              (pullReduction l E f).hom.app (DerivedCategory.Q.obj P) ≫
              (red l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
              (redFactors l E X).hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P)) =
          (dpull l E f).map cY ≫ (dpull l E f).map iY ≫
            ((pull l E f).mapDerivedCategoryFactors.hom.app ((strictRed l E Y).obj P) ≫
              DerivedCategory.Q.map ((strictPullReduction l E f).hom.app P)) := by
      convert congrArg (fun q ↦ (dpull l E f).map cY ≫ (dpull l E f).map iY ≫ q) hpr using 1 <;>
        dsimp [H, pullReduction]
    have hfac := (pull l E f).mapDerivedCategoryFactors_hom_naturality inrY
    dsimp [iY] at hpr'
    have hfac' :
        (pull l E f).mapDerivedCategory.map
            (DerivedCategory.Q.map
              inrY) ≫
          (pull l E f).mapDerivedCategoryFactors.hom.app
            ((strictRed l E Y).obj P) =
        (pull l E f).mapDerivedCategoryFactors.hom.app
            (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            (((pull l E f).mapHomologicalComplex (.up ℤ)).map
              inrY) := by
      exact hfac
    dsimp [dpull] at hpr'
    conv_rhs at hpr' =>
      simp only [Category.assoc]
      rw [reassoc_of% hfac']
    have hforward' :
        (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫
            (dconstant l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
            (constant l E X).mapDerivedCategoryFactors.hom.app
              ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).hom.app P) =
          (pull l E f).mapDerivedCategory.map cY ≫
            (pull l E f).mapDerivedCategoryFactors.hom.app
              (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) := by
      have hh := congrArg
        (fun q ↦ (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫ q)
        hforward
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hh.symm
    have hhinr :
        DerivedCategory.Q.map
              (((pull l E f).mapHomologicalComplex (.up ℤ)).map inrY) ≫
            DerivedCategory.Q.map ((strictPullReduction l E f).hom.app P) =
          DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map inrX := by
      dsimp [inrY, inrX]
      change _ = DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P) ≫
        DerivedCategory.Q.map ((strictAugmentation l E X).app
          ((H.mapHomologicalComplex (.up ℤ)).obj P))
      simpa only [Functor.map_comp, strictRed, strictAugmentation] using
        congrArg DerivedCategory.Q.map (hinr P)
    have hroute :
        (pull l E f).mapDerivedCategory.map cY ≫
            (pull l E f).mapDerivedCategoryFactors.hom.app
              (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              (((pull l E f).mapHomologicalComplex (.up ℤ)).map inrY) ≫
            DerivedCategory.Q.map ((strictPullReduction l E f).hom.app P) =
          (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫
            (dconstant l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
            (constant l E X).mapDerivedCategoryFactors.hom.app
              ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map inrX := by
      have hcancel :
          (pull l E f).mapDerivedCategory.map cY ≫
              (pull l E f).mapDerivedCategoryFactors.hom.app
                (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex
                  (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P) ≫
              DerivedCategory.Q.map inrX =
            (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫
              (dconstant l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
              (constant l E X).mapDerivedCategoryFactors.hom.app
                ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
              DerivedCategory.Q.map inrX := by
        have hh := congrArg
          (fun q ↦ q ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map inrX) hforward'
        have he := (NatIso.mapHomologicalComplex
          (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).hom_inv_id_app P
        convert hh.symm using 1 <;>
          simp only [dconstant, dpull, Functor.comp_obj, Category.assoc,
            Iso.hom_inv_id_app, Functor.map_id, Category.comp_id,
            ← NatTrans.mapHomologicalComplex_comp]
        have hsymm :
            NatIso.mapHomologicalComplex
                (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ) =
              (NatIso.mapHomologicalComplex
                (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).symm := by
          rfl
        have hmap :
            DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex
                  (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).hom.app P) ≫
              DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex
                  (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P) =
            𝟙 _ := by
          rw [hsymm]
          rw [← Functor.map_comp]
          simp
        have hmap' := hmap
        rw [hsymm]
        rw [hsymm] at hmap'
        rw [← Category.assoc
          (DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).hom.app P))
          (DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).symm.hom.app P))
          (DerivedCategory.Q.map inrX)]
        rw [hmap']
        simp
      rw [hhinr]
      exact hcancel
    dsimp [dpull]
    simpa only [dconstant, dpull, augmentation, strictAugmentation,
      Functor.map_comp, cY, iY, inrY, Functor.whiskerRight_app,
      Localization.liftNatTrans_app, Localization.Lifting.iso, Category.assoc] using
      (hpr'.trans hroute).trans hbetaSimpl.symm
  intro M
  have hm := congr_app hab M
  exact hm

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
