/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarCompositionPrelude

import all WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarCompositionSupportRealization
import WeilConjectures.AlgebraicGeometry.ScalarReductionBalancingComposition
import WeilConjectures.AlgebraicGeometry.StrictScalarComparisonSelection
import WeilConjectures.AlgebraicGeometry.StrictImageReindexComposition
import all WeilConjectures.AlgebraicGeometry.OrdinaryOpenScalarComposition

/-! # Unrestricted composition of strict compact-support scalar arrows

This proved factorization of the strict composition calculation applies before
finite-field geometry or finite-Tor hypotheses are imposed. It supplies the
composition equation used in the identity-unit cancellation argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

private theorem arrow_app_realization
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (arrow l E F i c S S' e he hepos).app M =
      (T l E F i Y).map ((supportModel l E c S).hom.app M) ≫
        (comparison l E F i c).app ((reduction l E X S).obj M) ≫
        (image l F c).map ((reductionBalancing l E F i X S S' e he hepos).hom.app M) ≫
        (reindexImage l F c e hepos).inv.app
          ((reduction l F X S').obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
        (subsequence l F Y e).map ((supportModel l F c S').inv.app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) := by
  unfold arrow
  rfl


private theorem image_composition_unrestricted {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (compositionTower l E F i L j Y).hom.app ((image l E c).obj K) ≫
        (comparison l E L (j.comp i) c).app K =
      (T l F L j Y).map ((comparison l E F i c).app K) ≫
        (comparison l F L j c).app ((T l E F i X).obj K) ≫
        (image l L c).map ((compositionTower l E F i L j X).hom.app K) := by
  unfold comparison
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  have hp := compositionProper l E F i L j c.g
    ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i).obj K)
  have ho := compositionOpen l E F i L j c.i K
  have hn := (proper l F L j c.g).naturality ((openTensor l E F i c.i).app K)
  simp only [Functor.comp_obj]
  change (compositionTower l E F i L j Y).hom.app
      ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g).obj
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i).obj K)) ≫
      (proper l E L (j.comp i) c.g).app
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i).obj K) ≫ _ = _
  rw [reassoc_of% hp]
  rw [← Functor.map_comp]
  rw [ho]
  simp only [Functor.map_comp, Functor.comp_obj]
  rw [← reassoc_of% hn]
  simp only [image, Functor.comp_map, Functor.comp_obj]


private theorem supportRealization_coherence_unrestricted {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (comparison l F L j c).app
        ((T l E F i X).obj ((reduction l E X SE).obj M)) ≫
      (image l L c).map ((compositionTower l E F i L j X).hom.app
        ((reduction l E X SE).obj M)) ≫
      (image l L c).map
        ((reductionBalancing l E L (j.comp i) X SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos)).hom.app M) ≫
      (reindexImage l L c (h * e) (one_le_mul hhpos hepos)).inv.app
        ((reduction l L X SL).obj
          ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)) ≫
      (subsequence l L Y (h * e)).map
        ((supportModel l L c SL).inv.app
          ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)) =
    (T l F L j Y).map
        ((image l F c).map
          ((reductionBalancing l E F i X SE SF e he hepos).hom.app M)) ≫
      (T l F L j Y).map
        ((reindexImage l F c e hepos).inv.app
          ((reduction l F X SF).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (T l F L j Y).map
        ((subsequence l F Y e).map
          ((supportModel l F c SF).inv.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (compositionSelection l F L j Y e).hom.app
        ((support l F c SF).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
      (subsequence l L Y e).map
        ((arrow l F L j c SF SL h hh hhpos).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
      (compositionRetained l L Y e h hepos hhpos).hom.app
        ((support l L c SL).obj
          ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (subsequence l L Y (h * e)).map
        ((support l L c SL).map
          ((compositionCompleted l E F i L j X).hom.app M)) := by
  have hb := reductionBalancing_composition l E F i L j X SE SF SL
    e h he hepos hh hhpos M
  have hs := comparison_selection l F L j c e hepos
    ((reduction l F X SF).obj
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
  have hr := reindexImage_composition l L c e h hepos hhpos
    ((reduction l L X SL).obj
      ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))
  have hm := (supportModel l L c SL).inv.naturality
    ((compositionCompleted l E F i L j X).hom.app M)
  have hp := support_pasting
    (image l F c) (image l L c) (T l F L j X) (T l F L j Y)
    (subsequence l F X e) (subsequence l F Y e)
    (subsequence l L X e) (subsequence l L X h) (subsequence l L X (h * e))
    (subsequence l L Y e) (subsequence l L Y h) (subsequence l L Y (h * e))
    (comparison l F L j c)
    (compositionSelection l F L j X e) (compositionSelection l F L j Y e)
    (reindexImage l F c e hepos).symm
    (reindexImage l L c e hepos).symm (reindexImage l L c h hhpos).symm
    (reindexImage l L c (h * e) (one_le_mul hhpos hepos)).symm
    (compositionRetained l L X e h hepos hhpos)
    (compositionRetained l L Y e h hepos hhpos)
    ((reductionBalancing l E F i X SE SF e he hepos).hom.app M)
    ((reductionBalancing l F L j X SF SL h hh hhpos).hom.app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((compositionTower l E F i L j X).hom.app ((reduction l E X SE).obj M) ≫
      (reductionBalancing l E L (j.comp i) X SE SL (h * e)
        (compositionRamification l E F i L j e h he hh)
        (one_le_mul hhpos hepos)).hom.app M)
    ((reduction l L X SL).map ((compositionCompleted l E F i L j X).hom.app M))
    ((support l L c SL).map ((compositionCompleted l E F i L j X).hom.app M))
    ((supportModel l F c SF).app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((supportModel l L c SL).app
      ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))
    ((supportModel l L c SL).app
      ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M))
    hb hs hr hm
  simpa only [Functor.comp_obj, Functor.map_comp, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    arrow, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using hp


/-- Strict scalar arrows compose on arbitrary schemes and arbitrary derived inputs.
Source: Stacks 07A6, 0E8I and 0940; auxiliary strict-scalar composition Steps 3--6.
(blueprint: lem-pur-compact-support-strict-scalar-arrow-composition).
Proof: paste the proper and open scalar-factor composition equations using
naturality of the proper factor. Reduction balancing composes through the tensor
and selection associators. Move selection through the image comparison, compose
the two image reindexing maps, and use naturality of the support model. The proved
categorical support-pasting identity combines these three equations. Expanding
arrow and moving the first support-model map through the tensor associator gives
the displayed equation. No geometric finiteness or finite-Tor assumption is used. -/
theorem strictScalarArrowComposition {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X))
    :
    (compositionTower l E F i L j Y).hom.app ((support l E c SE).obj M) ≫
        (arrow l E L (j.comp i) c SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos)).app M =
      (T l F L j Y).map ((arrow l E F i c SE SF e he hepos).app M) ≫
        (compositionSelection l F L j Y e).hom.app
          ((support l F c SF).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
        (subsequence l L Y e).map
          ((arrow l F L j c SF SL h hh hhpos).app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
        (compositionRetained l L Y e h hepos hhpos).hom.app
          ((support l L c SL).obj
            ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
        (subsequence l L Y (h * e)).map
          ((support l L c SL).map ((compositionCompleted l E F i L j X).hom.app M)) := by
  have hcomp := image_composition_unrestricted l E F i L j c
    ((reduction l E X SE).obj M)
  have hcoh := supportRealization_coherence_unrestricted l E F i L j c SE SF SL e h
    he hepos hh hhpos M
  rw [arrow_app_realization l E L (j.comp i) c SE SL (h * e)
    (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos) M,
    arrow_app_realization l E F i c SE SF e he hepos M,
    arrow_app_realization l F L j c SF SL h hh hhpos
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)]
  simp only [Functor.map_comp]
  have hnat := (compositionTower l E F i L j Y).hom.naturality
    ((supportModel l E c SE).hom.app M)
  rw [← reassoc_of% hnat]
  rw [reassoc_of% hcomp]
  rw [hcoh]
  rw [arrow_app_realization l F L j c SF SL h hh hhpos
    ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)]
  simp only [Functor.map_comp, Category.assoc]



set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem selected_comparison_unit
    {A B : Type*} [Category A] [Category B]
    (H : A ⥤ B) (C : A ⥤ A) (T S : B ⥤ B)
    (u : C ≅ 𝟭 A) (v : T ≅ 𝟭 B) (s : S ≅ 𝟭 B)
    (κ : H ⋙ T ≅ C ⋙ H ⋙ S)
    (σ : S ⋙ T ≅ T ⋙ S) (q : S ⋙ S ≅ S)
    (hσ : ∀ N, σ.hom.app N ≫ s.hom.app (T.obj N) = T.map (s.hom.app N))
    (hq : ∀ N, q.hom.app N = S.map (s.hom.app N))
    (hc : ∀ M, T.map (v.hom.app (H.obj M)) ≫ κ.hom.app M =
      T.map (κ.hom.app M) ≫ σ.hom.app (H.obj (C.obj M)) ≫
        S.map (κ.hom.app (C.obj M)) ≫ q.hom.app (H.obj (C.obj (C.obj M))) ≫
        S.map (H.map (C.map (u.hom.app M)))) (M : A) :
    κ.hom.app M ≫ s.hom.app (H.obj (C.obj M)) ≫ H.map (u.hom.app M) =
      v.hom.app (H.obj M) := by
  let β : H ⋙ T ≅ C ⋙ H :=
    κ ≪≫ Functor.isoWhiskerLeft (C ⋙ H) s ≪≫ Functor.rightUnitor (C ⋙ H)
  have hβ (N : A) : β.hom.app N =
      κ.hom.app N ≫ s.hom.app (H.obj (C.obj N)) := by
    simp only [β, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj]
    erw [Category.comp_id]
  have hcomp : T.map (v.hom.app (H.obj M)) ≫ β.hom.app M =
      T.map (β.hom.app M) ≫ β.hom.app (C.obj M) ≫
        H.map (C.map (u.hom.app M)) := by
    rw [hβ, ← Category.assoc, hc]
    simp only [Category.assoc]
    have ns : S.map (H.map (C.map (u.hom.app M))) ≫
        s.hom.app (H.obj (C.obj M)) =
      s.hom.app (H.obj (C.obj (C.obj M))) ≫ H.map (C.map (u.hom.app M)) :=
        s.hom.naturality _
    rw [ns]
    rw [hq]
    rw [← S.map_comp_assoc]
    have ns' : S.map (κ.hom.app (C.obj M) ≫
        s.hom.app (H.obj (C.obj (C.obj M)))) ≫
        s.hom.app (H.obj (C.obj (C.obj M))) =
      s.hom.app (T.obj (H.obj (C.obj M))) ≫
        (κ.hom.app (C.obj M) ≫ s.hom.app (H.obj (C.obj (C.obj M)))) :=
          s.hom.naturality _
    rw [reassoc_of% ns']
    rw [reassoc_of% hσ]
    simp only [hβ, T.map_comp, Category.assoc]
  have hn := β.hom.naturality (u.hom.app M)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hβ]
  exact target_unit_of_composition T v (β.hom.app M) (β.hom.app (C.obj M))
    (H.map (u.hom.app M)) (H.map (C.map (u.hom.app M)))
    (H.map (C.map (u.hom.app M))) (T.map (v.hom.app (H.obj M)))
    rfl rfl hcomp hn

private theorem localized_iso_refl
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory :=
  Iso.ext Functor.mapDerivedCategoryNatIso_refl

private theorem derived_left_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ A) (F : A ⥤ B)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (ρ : U ≅ 𝟭 A) (K : DerivedCategory A) :
    ((Functor.mapDerivedCategoryCompIso U F).inv.app K ≫
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight ρ F)).hom.app K) =
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app K)
        := by
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight ρ F) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U F).hom.app K)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, NatTrans.comp_app, F.mapDerivedCategory.map_comp]
  rw [← reassoc_of% hn, hu]
  erw [Category.comp_id]

private theorem identity_selection_compositor {A : Type*} [Category A]
    (U : A ⥤ A) (h : U = 𝟭 A) (h' : U ⋙ U = U) :
    eqToIso h' = Functor.isoWhiskerRight (eqToIso h) U := by
  subst U
  rfl

end WeilConjectures.PurStrictScalar
