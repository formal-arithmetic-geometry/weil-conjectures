/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale

/-! # Rees coordinates for a vector-bundle section

Source: smooth-purity, Agreement on the model, standard-pair computation.
(blueprint: lem-pur-vector-section-rees-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The constant vector family, its section, and its two fibre embeddings.
Every map is constructed by the pullback universal property. -/
def vectorReesFibre (B : Scheme.{u}) [IsNoetherian B] (d : ℕ)
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B) :
    VectorBundleZeroSection.scheme B d F ⟶
      pullback (VectorBundleZeroSection.π B d F)
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) :=
  pullback.lift (𝟙 _) (VectorBundleZeroSection.π B d F ≫ i)
    (by rw [Category.id_comp, Category.assoc, hi, Category.comp_id])

/-- The zero section of the constant vector family over the affine line. -/
def vectorReesZero (B : Scheme.{u}) [IsNoetherian B] (d : ℕ)
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    AffineSpace (ULift.{u} (Fin 1)) B ⟶
      pullback (VectorBundleZeroSection.π B d F)
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) :=
  pullback.lift ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫
    VectorBundleZeroSection.zero B d F) (𝟙 _)
    (by rw [Category.assoc, (VectorBundleZeroSection.zero_spec B d F).1,
      Category.comp_id, Category.id_comp])

/-- A geometric trivialization of the actual extended-Rees family. The endpoint equations
refer to the actual one-fibre and associated-graded zero-fibre inclusions, so the normal
coordinates cannot be changed independently of the source coordinates. -/
structure VectorReesModel {T B : Scheme.{u}} [IsNoetherian B] (d : ℕ)
    (g : T ⟶ B) (s : B ⟶ T) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (e : VectorBundleZeroSection.scheme B d F ≅ T) where
  normal : VectorBundleZeroSection.scheme B d F ≅ s.ker.normalCone
  normal_proj : normal.hom ≫ Scheme.Hom.normalConeProj g s =
    VectorBundleZeroSection.π B d F
  normal_zero : VectorBundleZeroSection.zero B d F ≫ normal.hom = s.normalConeZeroSection
  family : pullback (VectorBundleZeroSection.π B d F)
    (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≅ s.ker.deformationSpace
  family_proj : family.hom ≫ Scheme.Hom.deformationSpaceProj g s = pullback.snd _ _
  family_zero : vectorReesZero B d F ≫ family.hom = s.deformationSpaceSection
  one : vectorReesFibre B d F (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)
      (AffineSpace.oneSection_comp_over _ B) ≫ family.hom =
    e.hom ≫ Scheme.Hom.deformationSpaceOneFibre g s
  zero : vectorReesFibre B d F (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)
      (AffineSpace.zeroSection_comp_over _ B) ≫ family.hom =
    normal.hom ≫ s.ker.normalConeToDeformationSpace

private theorem vectorReesEndpoint {B D N : Scheme.{u}} [IsNoetherian B] (d : ℕ)
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (f : D ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (t : AffineSpace (ULift.{u} (Fin 1)) B ⟶ D)
    (family : pullback (VectorBundleZeroSection.π B d F)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≅ D)
    (hf : family.hom ≫ f = pullback.snd _ _)
    (hz : vectorReesZero B d F ≫ family.hom = t)
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    (q : N ⟶ B) (v : N ⟶ D) (z : B ⟶ N)
    (sq : IsPullback v q f i) (hs : z ≫ q = 𝟙 B) (hv : z ≫ v = i ≫ t) :
    ∃ e : VectorBundleZeroSection.scheme B d F ≅ N,
      e.hom ≫ q = VectorBundleZeroSection.π B d F ∧
      VectorBundleZeroSection.zero B d F ≫ e.hom = z ∧
      vectorReesFibre B d F i hi ≫ family.hom = e.hom ≫ v := by
  let π := VectorBundleZeroSection.π B d F
  let a := AffineSpace (ULift.{u} (Fin 1)) B ↘ B
  let u := vectorReesFibre B d F i hi
  have outer : IsPullback (u ≫ pullback.fst π a) π π (i ≫ a) := by
    have hu : u ≫ pullback.fst π a = 𝟙 _ := pullback.lift_fst _ _ _
    have hi' : i ≫ a = 𝟙 B := hi
    rw [hu, hi']
    exact IsPullback.id_horiz π
  have P : IsPullback u π (pullback.snd π a) i :=
    IsPullback.of_right outer (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π a)
  have Q : IsPullback (u ≫ family.hom) π f i := by
    have hh := P.paste_horiz (IsPullback.of_horiz_isIso
      (show CommSq family.hom (pullback.snd π a) f (𝟙 _) from
        ⟨hf.trans (Category.comp_id _).symm⟩))
    change IsPullback (u ≫ family.hom) π f (i ≫ 𝟙 _) at hh
    rwa [Category.comp_id] at hh
  let e := Q.isoIsPullback _ _ sq
  have heq : e.hom ≫ q = π := Q.isoIsPullback_hom_snd _ _ sq
  have hev : e.hom ≫ v = u ≫ family.hom := Q.isoIsPullback_hom_fst _ _ sq
  have hzu : VectorBundleZeroSection.zero B d F ≫ u = i ≫ vectorReesZero B d F := by
    apply pullback.hom_ext
    · dsimp only [u, vectorReesFibre, vectorReesZero]
      simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [← Category.assoc, hi, Category.id_comp]
    · dsimp only [u, vectorReesFibre, vectorReesZero]
      simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, (VectorBundleZeroSection.zero_spec B d F).1,
        Category.id_comp]
  refine ⟨e, heq, ?_, hev.symm⟩
  apply sq.hom_ext
  · rw [Category.assoc, hev, ← Category.assoc, hzu, Category.assoc, hz]
    exact hv.symm
  · rw [Category.assoc, heq, (VectorBundleZeroSection.zero_spec B d F).1, hs]

/-- A globally framed vector presentation supplies an actual constant Rees family.
The source presentation in the conclusion is obtained from the actual fibre at one.
Source: smooth-purity, Agreement on the model; DNC section geometry (4).
(blueprint: lem-pur-vector-section-rees-coordinates).

Proof: identify the pair with the standard affine zero section using the two given
presentations. The coefficientwise Rees comparison is a pullback of that isomorphism,
hence an isomorphism. Compose with the published standard-pair Rees isomorphism.
The pullback of the bundle frame identifies the constant vector family with the same
affine space over the line. Both maps preserve projection and augmentation, hence
construct the required family isomorphism and its section equality. Its fibre pullbacks
at one and zero give the source and normal isomorphisms. Their projection and inclusion
equations are the two universal-property equations. The section equalities follow by
pullback extensionality. Thus no separate calculation of the one-fibre coordinates is
needed, and empty frames and empty bases satisfy the same universal properties. -/
theorem vectorSection_reesCoordinates {T B : Scheme.{u}} [IsNoetherian B] (d : ℕ)
    (g : T ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (s : B ⟶ T) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (c : VectorBundleZeroSection.scheme B d F ≅ AffineSpace (ULift.{u} (Fin d)) B)
    (wc : c.hom ≫ (AffineSpace (ULift.{u} (Fin d)) B ↘ B) =
      VectorBundleZeroSection.π B d F)
    (zc : VectorBundleZeroSection.zero B d F ≫ c.hom =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) B)
    (e : VectorBundleZeroSection.scheme B d F ≅ T)
    (we : e.hom ≫ g = VectorBundleZeroSection.π B d F)
    (ze : VectorBundleZeroSection.zero B d F ≫ e.hom = s) :
    ∃ (e' : VectorBundleZeroSection.scheme B d F ≅ T)
      (_we' : e'.hom ≫ g = VectorBundleZeroSection.π B d F)
      (_ze' : VectorBundleZeroSection.zero B d F ≫ e'.hom = s),
      Nonempty (VectorReesModel d g s F e') := by
  let I := ULift.{u} (Fin d)
  let A := AffineSpace (ULift.{u} (Fin 1)) B
  let a := A ↘ B
  let π := VectorBundleZeroSection.π B d F
  let z := VectorBundleZeroSection.zero B d F
  let p := AffineSpace I B ↘ B
  let z₀ := AffineSpace.zeroSection I B
  let r := e.symm ≪≫ c
  have hr : r.hom ≫ p = g := by
    change e.inv ≫ c.hom ≫ p = g
    rw [wc, ← we, Iso.inv_hom_id_assoc]
  have hsr : s ≫ r.hom = (𝟙 B) ≫ z₀ := by
    change s ≫ e.inv ≫ c.hom = (𝟙 B) ≫ z₀
    rw [← ze, Category.assoc, Iso.hom_inv_id_assoc, zc, Category.id_comp]
  have : SmoothOfRelativeDimension d p := by
    simpa only [I, Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin] using
      AffineSpace.smoothOfRelativeDimension_over I B
  have H := AlgebraicGeometry.SectionReesBaseChange.etale d p z₀
    (AffineSpace.zeroSection_over I B) r.hom s
    (by rw [hr]; exact hs) hsr (IsPullback.of_vert_isIso ⟨hsr⟩)
  let ρ := AlgebraicGeometry.SectionReesBaseChange.pairMap z₀ s r.hom (𝟙 B) hsr
  have : IsIso ρ := H.1.isIso_fst_of_isIso
  let f := Scheme.Hom.deformationSpaceProj g s
  let t := s.deformationSpaceSection
  have hρ : ρ ≫ Scheme.Hom.deformationSpaceProj p z₀ = f := by
    have hh := H.2.2.1.1
    simpa only [hr, AffineSpace.map_id, Category.comp_id] using hh
  have hρz : t ≫ ρ = z₀.deformationSpaceSection := by
    have hh := H.2.2.1.2.1
    simpa only [AffineSpace.map_id, Category.id_comp] using hh
  let Φ := ρ ≫ Scheme.Hom.deformationSpaceToAffineSpace I B
  have : IsIso Φ := inferInstance
  have hΦ : Φ ≫ (AffineSpace I A ↘ A) = f := by
    change (ρ ≫ Scheme.Hom.deformationSpaceToAffineSpace I B) ≫ _ = f
    rw [Category.assoc, Scheme.Hom.deformationSpaceToAffineSpace_over, hρ]
  have hΦz : t ≫ Φ = AffineSpace.zeroSection I A := by
    change t ≫ ρ ≫ Scheme.Hom.deformationSpaceToAffineSpace I B = _
    rw [← Category.assoc, hρz,
      Scheme.Hom.deformationSpaceSection_comp_deformationSpaceToAffineSpace]
  have PC : IsPullback (pullback.fst π a ≫ c.hom) (pullback.snd π a) p a := by
    have hh := (IsPullback.of_hasPullback π a).paste_horiz
      (IsPullback.of_horiz_isIso
        (show CommSq c.hom π p (𝟙 B) from ⟨wc.trans (Category.comp_id _).symm⟩))
    change IsPullback (pullback.fst π a ≫ c.hom) (pullback.snd π a) p (a ≫ 𝟙 B) at hh
    rwa [Category.comp_id] at hh
  let PA := AffineSpace.isPullback_map (n := I) a
  let C := PC.isoIsPullback _ _ PA
  have hC : C.hom ≫ (AffineSpace I A ↘ A) = pullback.snd π a :=
    PC.isoIsPullback_hom_snd _ _ PA
  have hCf : C.hom ≫ AffineSpace.map I a = pullback.fst π a ≫ c.hom :=
    PC.isoIsPullback_hom_fst _ _ PA
  have hCz : vectorReesZero B d F ≫ C.hom = AffineSpace.zeroSection I A := by
    apply PA.hom_ext
    · rw [Category.assoc, hCf, ← Category.assoc]
      change (vectorReesZero B d F ≫ pullback.fst π a) ≫ c.hom = _
      rw [show vectorReesZero B d F ≫ pullback.fst π a = a ≫ z from
        pullback.lift_fst _ _ _, Category.assoc, zc, AffineSpace.zeroSection_comp_map]
    · rw [Category.assoc, hC, AffineSpace.zeroSection_over]
      exact pullback.lift_snd _ _ _
  let D := asIso Φ
  let family := C ≪≫ D.symm
  have hf : family.hom ≫ f = pullback.snd π a := by
    have hi : D.inv ≫ f = (AffineSpace I A ↘ A) := (Iso.inv_comp_eq _).mpr hΦ.symm
    change C.hom ≫ D.inv ≫ f = _
    rw [hi, hC]
  have hz : vectorReesZero B d F ≫ family.hom = t := by
    apply (cancel_mono D.hom).mp
    change (vectorReesZero B d F ≫ C.hom ≫ D.inv) ≫ D.hom = t ≫ D.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hCz.trans hΦz.symm
  obtain ⟨e', we', ze', he'⟩ := vectorReesEndpoint d F f t family hf hz
    (AffineSpace.oneSection _ B) (AffineSpace.oneSection_comp_over _ B) g
    (Scheme.Hom.deformationSpaceOneFibre g s) s
    (Scheme.Hom.isPullback_deformationSpaceOneFibre g s) hs
    (Scheme.Hom.comp_deformationSpaceOneFibre hs)
  obtain ⟨n, wn, zn, hn⟩ := vectorReesEndpoint d F f t family hf hz
    (AffineSpace.zeroSection _ B) (AffineSpace.zeroSection_comp_over _ B)
    (Scheme.Hom.normalConeProj g s) s.ker.normalConeToDeformationSpace
    s.normalConeZeroSection (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
    (Scheme.Hom.normalConeZeroSection_normalConeProj hs)
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace
  exact ⟨e', we', ze', ⟨{
    normal := n
    normal_proj := wn
    normal_zero := zn
    family := family
    family_proj := hf
    family_zero := hz
    one := he'
    zero := hn }⟩⟩

end WeilConjectures.PurityFiniteSetting
