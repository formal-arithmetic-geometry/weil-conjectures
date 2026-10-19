/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Transporting a scalar-adjunction mate through localization comparisons

Source: Stacks 07A6 and 07A4; blueprint main-20261015, direct-image proof, Step 1.
(blueprint: lem-sp-direct-image-tensor-pullback-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

private theorem normalizedMate
    {A B C D AD BD CD DD : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category AD] [Category BD] [Category CD] [Category DD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (QC : C ⥤ CD) (QD : D ⥤ DD)
    (L : A ⥤ C) (R : B ⥤ A) (H : B ⥤ D) (S : D ⥤ C)
    (Ld : AD ⥤ CD) (Rd : BD ⥤ AD) (Hd : BD ⥤ DD) (Sd : DD ⥤ CD)
    (E : AD ⥤ BD) (F : CD ⥤ DD) (a : E ⊣ Rd) (a' : F ⊣ Sd)
    (l : QA ⋙ Ld ≅ L ⋙ QC) (r : QB ⋙ Rd ≅ R ⋙ QA)
    (h : QB ⋙ Hd ≅ H ⋙ QD) (s : QD ⋙ Sd ≅ S ⋙ QC)
    (b : ∀ K, L.obj (R.obj K) ⟶ S.obj (H.obj K)) (bd : Rd ⋙ Ld ⟶ Hd ⋙ Sd)
    (P : A) (EP : B) (FP : D)
    (u : P ⟶ R.obj EP) (v : L.obj P ⟶ S.obj FP)
    (e : E.obj (QA.obj P) ⟶ QB.obj EP)
    (d : F.obj (QC.obj (L.obj P)) ⟶ QD.obj FP)
    (hu : a.unit.app (QA.obj P) ≫ Rd.map e ≫ r.hom.app EP = QA.map u)
    (hv : a'.unit.app (QC.obj (L.obj P)) ≫ Sd.map d ≫ s.hom.app FP = QC.map v)
    (hb : bd.app (QB.obj EP) ≫ Sd.map (h.hom.app EP) ≫ s.hom.app (H.obj EP) =
      Ld.map (r.hom.app EP) ≫ l.hom.app (R.obj EP) ≫ QC.map (b EP))
    (g : H.obj EP ⟶ FP)
    (hg : L.map u ≫ b EP ≫ S.map g = v) :
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ bd)).natTrans.app (QA.obj P) ≫
      Hd.map e ≫ h.hom.app EP ≫ QD.map g =
        F.map (l.hom.app P) ≫ d := by
  apply (a'.homEquiv _ _).injective
  apply (cancel_mono (s.hom.app FP)).1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hm := unit_mateEquiv_symm a a' (TwoSquare.mk _ _ _ _ bd) (QA.obj P)
  change Ld.map (a.unit.app (QA.obj P)) ≫ bd.app (E.obj (QA.obj P)) =
    a'.unit.app (Ld.obj (QA.obj P)) ≫ Sd.map
      (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ bd)).natTrans.app (QA.obj P)) at hm
  rw [← Category.assoc, ← hm]
  simp only [Category.assoc]
  have hn := bd.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (bd.app _) (Sd.map (Hd.map e)), ← hn]
  simp only [Category.assoc]
  have hs := s.hom.naturality g
  dsimp only [Functor.comp_map] at hs
  rw [hs]
  slice_lhs 3 5 => rw [hb]
  simp only [Category.assoc]
  rw [← Ld.map_comp_assoc, ← Ld.map_comp_assoc]
  simp only [Category.assoc]
  rw [hu]
  have hl := l.hom.naturality u
  dsimp only [Functor.comp_map] at hl
  rw [← Category.assoc, hl]
  simp only [Category.assoc]
  rw [← QC.map_comp, ← QC.map_comp, hg]
  have hf := a'.unit.naturality (l.hom.app P)
  dsimp only [Functor.comp_map, Functor.id_map] at hf
  erw [← Category.assoc (a'.unit.app _), ← hf]
  simpa only [Category.assoc, Functor.comp_obj] using (congrArg (fun z ↦ l.hom.app P ≫ z) hv).symm

/-- A restriction/pullback square and normalized scalar units determine the localized
ordinary scalar mate. Only the ordinary unit equation and the factorization of the
restriction square are required.

Proof: transpose under the target scalar adjunction. The inverse-mate unit equation
moves the source unit across the derived restriction square. Naturality moves the
source comparison through that square, and its factorization replaces it by the
localized ordinary square. The two scalar-unit normalizations and the ordinary unit
identity identify the resulting maps. Transpose back and apply restriction.
Source: Stacks 07A6, 07A4; blueprint direct-image proof, Step 1
(blueprint: lem-sp-direct-image-tensor-pullback-localization). -/
theorem directImageChangeRing_tensorNormalization_localization
    {A B C D AD BD CD DD : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category AD] [Category BD] [Category CD] [Category DD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (QC : C ⥤ CD) (QD : D ⥤ DD)
    (L : A ⥤ C) (R : B ⥤ A) (H : B ⥤ D) (S : D ⥤ C)
    (Ld : AD ⥤ CD) (Rd : BD ⥤ AD) (Hd : BD ⥤ DD) (Sd : DD ⥤ CD)
    (E : AD ⥤ BD) (F : CD ⥤ DD) (a : E ⊣ Rd) (a' : F ⊣ Sd)
    (l : QA ⋙ Ld ≅ L ⋙ QC) (r : QB ⋙ Rd ≅ R ⋙ QA)
    (h : QB ⋙ Hd ≅ H ⋙ QD) (s : QD ⋙ Sd ≅ S ⋙ QC)
    (b : ∀ K, L.obj (R.obj K) ⟶ S.obj (H.obj K)) (bd : Rd ⋙ Ld ⟶ Hd ⋙ Sd)
    (P : A) (EP : B) (FP : D)
    (u : P ⟶ R.obj EP) (v : L.obj P ⟶ S.obj FP)
    (e : E.obj (QA.obj P) ⟶ QB.obj EP)
    (d : F.obj (QC.obj (L.obj P)) ⟶ QD.obj FP)
    (hu : a.unit.app (QA.obj P) ≫ Rd.map e ≫ r.hom.app EP = QA.map u)
    (hv : a'.unit.app (QC.obj (L.obj P)) ≫ Sd.map d ≫ s.hom.app FP = QC.map v)
    (hb : bd.app (QB.obj EP) ≫ Sd.map (h.hom.app EP) ≫ s.hom.app (H.obj EP) =
      Ld.map (r.hom.app EP) ≫ l.hom.app (R.obj EP) ≫ QC.map (b EP))
    (g : H.obj EP ⟶ FP)
    (hg : L.map u ≫ b EP ≫ S.map g = v)
    (θ : E ⋙ Hd ≅ Ld ⋙ F)
    (hθ : θ.inv = ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ bd)).natTrans) :
    Ld.map (Rd.map e ≫ r.hom.app EP) ≫ l.hom.app (R.obj EP) ≫
        QC.map (b EP ≫ S.map g) =
      bd.app (E.obj (QA.obj P)) ≫
        Sd.map (θ.hom.app (QA.obj P) ≫ F.map (l.hom.app P) ≫ d) ≫ s.hom.app FP := by
  have hh := normalizedMate QA QB QC QD L R H S Ld Rd Hd Sd E F a a'
    l r h s b bd P EP FP u v e d hu hv hb g hg
  rw [← hθ] at hh
  rw [← hh]
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  have hn := bd.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (bd.app _) (Sd.map (Hd.map e)), ← hn]
  simp only [Category.assoc]
  have hs := s.hom.naturality g
  dsimp only [Functor.comp_map] at hs
  rw [hs]
  slice_rhs 2 4 => rw [hb]
  simp only [Category.assoc]
