/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.SectionFiniteEtaleGenericSplit

/-! # Splitting the zero slice of the fixed formal test

Source: Stacks Project, Tags 0EYJ and 0EY9.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

private theorem normalization_open_comparison {C : Scheme.{u}} (W : C.Opens)
    (PA : W.toScheme.FiniteEtale) [QuasiCompact W.ι] [IsFinite PA.obj.hom] :
    ∃ i : PA.obj.left ≅ pullback (PA.obj.hom ≫ W.ι).fromNormalization W.ι,
      i.hom ≫ pullback.snd (PA.obj.hom ≫ W.ι).fromNormalization W.ι = PA.obj.hom := by
  let f := PA.obj.hom ≫ W.ι
  let k := pullback.snd f W.ι
  have H : IsPullback (𝟙 PA.obj.left) PA.obj.hom f W.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f]⟩
  have hk : IsFinite k := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite.{u}) H.isoPullback.hom]
    simpa only [k, H.isoPullback_hom_snd] using PA.property
  let := hk
  let i := H.isoPullback ≪≫ asIso k.toNormalization ≪≫ asIso (f.normalizationPullback W.ι)
  refine ⟨i, ?_⟩
  change H.isoPullback.hom ≫ k.toNormalization ≫
    f.normalizationPullback W.ι ≫ pullback.snd f.fromNormalization W.ι = _
  rw [f.normalizationPullback_snd]
  change H.isoPullback.hom ≫ (k.toNormalization ≫ k.fromNormalization) = _
  rw [k.toNormalization_fromNormalization]
  exact H.isoPullback_hom_snd

private theorem normalization_open_section {C B : Scheme.{u}} (W : C.Opens)
    (PA : W.toScheme.FiniteEtale) [QuasiCompact W.ι] [IsFinite PA.obj.hom]
    (b : B ⟶ W.toScheme) :
    ∃ e : pullback PA.obj.hom b ≅
        pullback (PA.obj.hom ≫ W.ι).fromNormalization (b ≫ W.ι),
      e.hom ≫ pullback.snd (PA.obj.hom ≫ W.ι).fromNormalization (b ≫ W.ι) =
        pullback.snd PA.obj.hom b := by
  obtain ⟨i, hi⟩ := normalization_open_comparison W PA
  have H : IsPullback
      (i.hom ≫ pullback.fst (PA.obj.hom ≫ W.ι).fromNormalization W.ι)
      PA.obj.hom (PA.obj.hom ≫ W.ι).fromNormalization W.ι := by
    refine IsPullback.of_iso_pullback ?_ i rfl hi
    constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc, hi]
  let H' := (IsPullback.of_hasPullback PA.obj.hom b).paste_horiz H
  exact ⟨H'.isoPullback, H'.isoPullback_hom_snd⟩

private theorem constant_cover_pullback {B T : Scheme.{u}}
    (G : Type (u + 1)) [Finite G] (v : B ⟶ T) :
    ∃ e : (∐ fun _ : G ↦ B) ≅ pullback (Sigma.desc (fun _ : G ↦ 𝟙 T)) v,
      e.hom ≫ pullback.snd (Sigma.desc (fun _ : G ↦ 𝟙 T)) v =
        Sigma.desc (fun _ : G ↦ 𝟙 B) := by
  let a : (∐ fun _ : G ↦ B) ⟶ (∐ fun _ : G ↦ T) :=
    Sigma.desc fun g : G ↦ v ≫ Sigma.ι (fun _ : G ↦ T) g
  have H : IsPullback a (Sigma.desc (fun _ : G ↦ 𝟙 B))
      (Sigma.desc (fun _ : G ↦ 𝟙 T)) v := by
    have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G ↦ T))
    have hs := hu.isPullback_of_isColimit_left (fun _ : G ↦ 𝟙 T)
      (Sigma.desc (fun _ : G ↦ 𝟙 T)) v (fun _ : G ↦ 𝟙 B)
      (fun _ : G ↦ v) (fun _ : G ↦ IsPullback.of_id_fst (f := v))
      (coproductIsCoproduct (fun _ : G ↦ B))
    simpa [Cofan.IsColimit.desc, coproductIsCoproduct, a] using hs.flip
  exact ⟨H.isoPullback, H.isoPullback_hom_snd⟩

private theorem restricted_pullback {F T B : Scheme.{u}} (r : F ⟶ T)
    (V : T.Opens) (z : B ⟶ V.toScheme) :
    ∃ e : pullback (r ∣_ V) z ≅ pullback r (z ≫ V.ι),
      e.hom ≫ pullback.snd r (z ≫ V.ι) = pullback.snd (r ∣_ V) z := by
  let H := (IsPullback.of_hasPullback (r ∣_ V) z).paste_horiz
    (isPullback_morphismRestrict r V).flip
  exact ⟨H.isoPullback, H.isoPullback_hom_snd⟩

private theorem composed_pullback {X Y Z B : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (v : B ⟶ Y) :
    ∃ e : pullback (pullback.snd f g) v ≅ pullback f (v ≫ g),
      e.hom ≫ pullback.snd f (v ≫ g) = pullback.snd (pullback.snd f g) v := by
  let H := (IsPullback.of_hasPullback (pullback.snd f g) v).paste_horiz
    (IsPullback.of_hasPullback f g)
  exact ⟨H.isoPullback, H.isoPullback_hom_snd⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Splitting over U first makes the minimality hypotheses unnecessary for this proof.
set_option trace.profiler true in
set_option maxHeartbeats 1800000 in
-- The nested normalization and iterated pullbacks require extra elaboration heartbeats.
/-- The normalization test is split on the zero slice of its punctured open.
This only gives an isomorphism after pulling back to the zero slice.

Source: Stacks Project, Tag 0EYJ (the rational section point and extended action);
Tag 0BQM (full faithfulness over a normal integral base).
(blueprint: lem-sbc-stalk-normalization-formal-zero-slice-split)

Proof: Minimality identifies the inverse image of U with the punctured spectrum
of the normal local ring A = O_{S,s}. On this open relative normalization
agrees with PA: PA is finite, hence integral, over C_U, and normalization
commutes with smooth base change along the open inclusion.
Extend the generic G-action to PA using generic-fibre full faithfulness.
Pull back along the given section on this punctured local base. The rational
point over the generic section and its G-translates give an isomorphism of
its generic fibre with the constant G-indexed cover: simple transitivity
makes the translates distinct and exhaustive. On the normal integral
punctured local base, extend that generic isomorphism and its inverse using
full faithfulness of finite etale restriction to the generic point (0BQM).
Uniqueness checks both inverse identities. The base compatibility of t and
its entire zero-section compatibility identify the zero slice of V with
this punctured base, and identify the pulled-back normalization cover with
the section pullback of PA. Pullback of the constant coproduct commutes with
this restriction. Transport the section-cover isomorphism through these
canonical pullback comparisons to get the displayed finite etale isomorphism.
This argument applies to zero variables and to disconnected torsors; it
makes no assertion about the cover away from the zero slice. -/
theorem GaloisCover.stalk_normalization_formal_zero_slice_split {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d))) ≫ t = τ →
      let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
      let F : Scheme.{u} := pullback n t
      let E : Scheme.{u} := ∐ (fun _ : G ↦ T)
      let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
      let r : F ⟶ T := pullback.snd n t
      let p : E ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
      let z := (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d)))) ∣_ V
      ∃ e : pullback (p ∣_ V) z ≅ pullback (r ∣_ V) z,
        e.hom ≫ pullback.snd (r ∣_ V) z = pullback.snd (p ∣_ V) z := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro d t hb hz
  let a := S.fromSpecStalk s
  let g := pullback.fst c a
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let n := pullback.snd f.fromNormalization g
  let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
  let r := pullback.snd n t
  let p := Sigma.desc (fun _ : G ↦ 𝟙 T)
  let V := (t ≫ g) ⁻¹ᵁ (c ⁻¹ᵁ U)
  let ζ := Spec.map (CommRingCat.ofHom
    (MvPowerSeries.constantCoeff (σ := Fin d) (R := S.presheaf.stalk s)))
  let z := ζ ∣_ V
  let v := z ≫ V.ι
  let Hc := (isPullback_morphismRestrict c U).flip
  let b : U.toScheme ⟶ (c ⁻¹ᵁ U).toScheme :=
    Hc.lift (U.ι ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  have hbι : b ≫ (c ⁻¹ᵁ U).ι = U.ι ≫ σ := by simp [b]
  let w := z ≫ ((t ≫ g) ∣_ (c ⁻¹ᵁ U))
  let wU := w ≫ (c ∣_ U)
  have hwι : w ≫ (c ⁻¹ᵁ U).ι = v ≫ t ≫ g := by
    simp only [w, Category.assoc, morphismRestrict_ι]
    rfl
  have hvσ : v ≫ t ≫ g = (ζ ⁻¹ᵁ V).ι ≫ a ≫ σ := by
    dsimp only [v, z]
    rw [morphismRestrict_ι, Category.assoc, ← Category.assoc ζ, hz]
    rw [pullback.lift_fst]
  have hwU : wU ≫ U.ι = (ζ ⁻¹ᵁ V).ι ≫ a := by
    dsimp only [wU]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      hwι, hvσ]
    simp [Category.assoc, hσ]
  have hwb : wU ≫ b = w := by
    apply (cancel_mono (c ⁻¹ᵁ U).ι).mp
    rw [Category.assoc, hbι, ← Category.assoc, hwU, hwι, hvσ]
    simp only [Category.assoc]
  have hsplit := GaloisCover.section_finiteEtale_generic_split.{u}
    hS c σ hσ G q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ b hbι
  obtain ⟨eS, heS⟩ := hsplit
  have hN : ∃ e : pullback PA.obj.hom (wU ≫ b) ≅
      pullback f.fromNormalization ((wU ≫ b) ≫ (c ⁻¹ᵁ U).ι),
      e.hom ≫ pullback.snd f.fromNormalization ((wU ≫ b) ≫ (c ⁻¹ᵁ U).ι) =
        pullback.snd PA.obj.hom (wU ≫ b) :=
    normalization_open_section.{u} (C := C) (B := (ζ ⁻¹ᵁ V).toScheme)
      (c ⁻¹ᵁ U) PA (wU ≫ b)
  obtain ⟨eN, heN⟩ := hN
  have heR₁ := restricted_pullback r V z
  obtain ⟨eR₁, heR₁⟩ := heR₁
  have heR₂ := composed_pullback n t v
  obtain ⟨eR₂, heR₂⟩ := heR₂
  have heR₃ := composed_pullback f.fromNormalization g (v ≫ t)
  obtain ⟨eR₃, heR₃⟩ := heR₃
  have heR₄ := composed_pullback PA.obj.hom b wU
  obtain ⟨eR₄, heR₄⟩ := heR₄
  have heP₁ := restricted_pullback p V z
  obtain ⟨eP₁, heP₁⟩ := heP₁
  have heP₂ := constant_cover_pullback G v
  obtain ⟨eP₂, heP₂⟩ := heP₂
  have heP₃ := constant_cover_pullback G wU
  obtain ⟨eP₃, heP₃⟩ := heP₃
  have hq : (v ≫ t) ≫ g = (wU ≫ b) ≫ (c ⁻¹ᵁ U).ι := by
    rw [hwb, hwι, Category.assoc]
  let eQ := pullback.congrHom (f₁ := f.fromNormalization) rfl hq
  have heQ : eQ.hom ≫
      pullback.snd f.fromNormalization ((wU ≫ b) ≫ (c ⁻¹ᵁ U).ι) =
      pullback.snd f.fromNormalization ((v ≫ t) ≫ g) := by
    dsimp only [eQ, pullback.congrHom, asIso_hom, pullback.map]
    rw [pullback.lift_snd]
    simp
  have heNi : eN.inv ≫ pullback.snd PA.obj.hom (wU ≫ b) =
      pullback.snd f.fromNormalization ((wU ≫ b) ≫ (c ⁻¹ᵁ U).ι) := by
    rw [← heN, eN.inv_hom_id_assoc]
  have heR₄i : eR₄.inv ≫ pullback.snd (pullback.snd PA.obj.hom b) wU =
      pullback.snd PA.obj.hom (wU ≫ b) := by
    rw [← heR₄, eR₄.inv_hom_id_assoc]
  let eR := eR₁ ≪≫ eR₂ ≪≫ eR₃ ≪≫ eQ ≪≫ eN.symm ≪≫ eR₄.symm
  have heR : eR.hom ≫ pullback.snd (pullback.snd PA.obj.hom b) wU =
      pullback.snd (r ∣_ V) z := by
    simp only [eR, Iso.trans_hom, Iso.symm_hom, Category.assoc, heR₄i, heNi, heQ]
    rw [heR₃, heR₂, heR₁]
  have heP₂i : eP₂.inv ≫ Sigma.desc (fun _ : G ↦ 𝟙 (ζ ⁻¹ᵁ V).toScheme) =
      pullback.snd p v := by
    rw [← heP₂, eP₂.inv_hom_id_assoc]
  let eP := eP₁ ≪≫ eP₂.symm ≪≫ eP₃
  have heP : eP.hom ≫ pullback.snd (Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme)) wU =
      pullback.snd (p ∣_ V) z := by
    simp only [eP, Iso.trans_hom, Iso.symm_hom, Category.assoc, heP₃, heP₂i]
    exact heP₁
  let m := pullback.map (Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme)) wU
    (pullback.snd PA.obj.hom b) wU eS.hom (𝟙 _) (𝟙 _)
    (by simpa using heS.symm) (by simp)
  have hm : m ≫ pullback.snd (pullback.snd PA.obj.hom b) wU =
      pullback.snd (Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme)) wU := by
    dsimp only [m, pullback.map]
    rw [pullback.lift_snd]
    simp
  have heRi : eR.inv ≫ pullback.snd (r ∣_ V) z =
      pullback.snd (pullback.snd PA.obj.hom b) wU := by
    rw [← heR, eR.inv_hom_id_assoc]
  refine ⟨eP ≪≫ asIso m ≪≫ eR.symm, ?_⟩
  change (eP.hom ≫ m ≫ eR.inv) ≫ pullback.snd (r ∣_ V) z = _
  rw [Category.assoc, Category.assoc, heRi, hm, heP]

end AlgebraicGeometry.Scheme
