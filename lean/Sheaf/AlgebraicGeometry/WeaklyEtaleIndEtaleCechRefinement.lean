/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

import Sheaf.AlgebraicGeometry.IndEtalePullbackCharts
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-! # Finite ind-étale refinements and their Čech terms

Source: Bhatt--Scholze, Theorem 2.3.4, Proposition 2.3.3 and Remark 4.1.3
(blueprint: lem-sfb-weakly-etale-indetale-cech-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem affine_indEtale_refinement {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [WeaklyEtale f] :
    ∃ (D : Scheme.{u}) (r : D ⟶ X),
      IsAffine D ∧ Surjective r ∧ proAffineEtale r ∧ proAffineEtale (r ≫ f) := by
  have hf : f.appTop.hom.WeaklyEtale :=
    (HasRingHomProperty.iff_of_isAffine (P := @WeaklyEtale)
      (Q := RingHom.WeaklyEtale) (f := f)).mp inferInstance
  obtain ⟨T, hT, g, hg, hflat, hcomp⟩ := hf.exists_indEtale_comp
  let D := Spec (CommRingCat.of T)
  let r : D ⟶ X := Spec.map (CommRingCat.ofHom g) ≫ X.isoSpec.inv
  have hs : Surjective (Spec.map (CommRingCat.ofHom g)) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom g)).mpr hflat).2
  refine ⟨D, r, inferInstance, inferInstance, ?_, ?_⟩
  · change proAffineEtale (Spec.map (CommRingCat.ofHom g) ≫ X.isoSpec.inv)
    rw [proAffineEtale.cancel_right_of_respectsIso]
    exact proAffineEtale_Spec_iff.mpr hg
  · have he : r ≫ f =
        Spec.map (CommRingCat.ofHom (g.comp f.appTop.hom)) ≫ Y.isoSpec.inv := by
      dsimp [r]
      rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
        ← Spec.map_comp]
    rw [he, proAffineEtale.cancel_right_of_respectsIso]
    exact proAffineEtale_Spec_iff.mpr hcomp

private theorem finite_affine_target_cover {U V : Scheme.{u}} [CompactSpace U]
    (b : U ⟶ V) :
    ∃ C : Scheme.OpenCover.{u} U, Finite C.I₀ ∧ ∀ a : C.I₀,
      IsAffine (C.X a) ∧ ∃ (W : V.Opens) (_hW : IsAffineOpen W)
        (f : C.X a ⟶ W.toScheme), f ≫ W.ι = C.f a ≫ b := by
  let B : U.OpenCover := V.affineCover.pullback₁ b
  let C : U.OpenCover := B.bind fun a ↦ (B.X a).affineCover
  have hC (a : C.I₀) : IsAffine (C.X a) ∧
      ∃ (W : V.Opens) (_hW : IsAffineOpen W) (f : C.X a ⟶ W.toScheme),
        f ≫ W.ι = C.f a ≫ b := by
    rcases a with ⟨i, j⟩
    have hA : IsAffine (C.X ⟨i, j⟩) := by
      change IsAffine ((B.X i).affineCover.X j)
      infer_instance
    refine ⟨hA, (V.affineCover.f i).opensRange, isAffineOpen_opensRange _,
      (B.X i).affineCover.f j ≫ V.affineCover.pullbackHom b i ≫
        (V.affineCover.f i).isoOpensRange.hom, ?_⟩
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι,
      Scheme.Cover.pullbackHom_map]
    rfl
  refine ⟨C.finiteSubcover, inferInstance, ?_⟩
  intro a
  change IsAffine (C.X (C.idx a.val)) ∧ _
  exact hC (C.idx a.val)

/-- The finite affine refinement and its affine target factorizations.

Source: Bhatt--Scholze, Theorem 2.3.4 and Remark 4.1.3
(blueprint: lem-sfb-weakly-etale-indetale-cech-refinement).

Proof: choose finite affine open covers of the target and of the inverse images of
those opens, then take a finite subcover of the source. On each affine map apply
`RingHom.WeaklyEtale.exists_indEtale_comp`;
the resulting spectrum map is faithfully flat and pro-affine-étale. Assemble the
finite family as a pro-étale cover and retain the affine target factorization.
-/
private theorem exists_finite_affine_indEtale_cover
    {U V : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [QuasiCompact b] [QuasiSeparated b] [WeaklyEtale b] :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U,
      Finite D.I₀ ∧ (∀ a : D.I₀, IsAffine (D.X a)) ∧
      (∀ a : D.I₀, ∃ (A : Scheme.{u}) (i : A ⟶ U) (r : D.X a ⟶ A),
        IsAffine A ∧ IsOpenImmersion i ∧ proAffineEtale r ∧ r ≫ i = D.f a) ∧
      ∀ a : D.I₀, ∃ (W : V.Opens) (_hW : IsAffineOpen W)
        (g : D.X a ⟶ W.toScheme), proAffineEtale g ∧ g ≫ W.ι = D.f a ≫ b := by
  classical
  obtain ⟨C, hfin, hC⟩ := finite_affine_target_cover b
  have hA (a : C.I₀) : IsAffine (C.X a) := (hC a).1
  choose W hW f hf using fun a ↦ (hC a).2
  have hWA (a : C.I₀) : IsAffine (W a).toScheme := hW a
  have hw (a : C.I₀) : WeaklyEtale (f a) := by
    have : WeaklyEtale (f a ≫ (W a).ι) := by rw [hf a]; infer_instance
    exact WeaklyEtale.of_comp (f a) (W a).ι
  choose X r hX hs hr hrf using fun a ↦ affine_indEtale_refinement (f a)
  let q (a : C.I₀) : X a ⟶ U := r a ≫ C.f a
  have hq (a : C.I₀) : WeaklyEtale (q a) := by
    have : WeaklyEtale (r a) := proAffineEtale_le_weaklyEtale _ (hr a)
    dsimp [q]
    infer_instance
  let D₀ : Scheme.Cover.{u} (Scheme.precoverage @WeaklyEtale) U :=
    Scheme.Cover.mkOfCovers C.I₀ X q (fun x ↦ by
      obtain ⟨a, y, rfl⟩ := C.exists_eq x
      obtain ⟨z, rfl⟩ := (hs a).surj y
      exact ⟨a, z, rfl⟩) hq
  have : Finite D₀.I₀ := hfin
  have (a : D₀.I₀) : QuasiCompact (D₀.f a) := by
    change QuasiCompact (q a)
    infer_instance
  let D : Scheme.Cover.{u} Scheme.proetalePrecoverage U := D₀.ofQuasiCompactCover
  refine ⟨D, hfin, hX, ?_, ?_⟩
  · intro a
    exact ⟨C.X a, C.f a, r a, hA a, inferInstance, hr a, rfl⟩
  · intro a
    refine ⟨W a, hW a, r a ≫ f a, hrf a, ?_⟩
    change (r a ≫ f a) ≫ (W a).ι = (r a ≫ C.f a) ≫ b
    simp only [Category.assoc, hf a]

private abbrev AffineIndEtaleCharts {X V : Scheme.{u}} (f : X ⟶ V) : Prop :=
  ∃ T : Scheme.OpenCover.{u} X, ∀ β : T.I₀,
    IsAffine (T.X β) ∧
    ∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : T.X β ⟶ W.toScheme),
      proAffineEtale g ∧ g ≫ W.ι = T.f β ≫ f

private theorem charts_of_iso {X Y V : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ V)
    (h : AffineIndEtaleCharts f) : AffineIndEtaleCharts (e.hom ≫ f) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.pushforwardIso e.inv, ?_⟩
  intro a
  obtain ⟨hA, W, hW, g, hg, he⟩ := hT a
  refine ⟨hA, W, hW, g, hg, ?_⟩
  change g ≫ W.ι = (T.f a ≫ e.inv) ≫ e.hom ≫ f
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he

private theorem charts_of_affine {X V : Scheme.{u}} [IsAffine X]
    (f : X ⟶ V) (h : ∃ (W : V.Opens) (_hW : IsAffineOpen W)
      (g : X ⟶ W.toScheme), proAffineEtale g ∧ g ≫ W.ι = f) :
    AffineIndEtaleCharts f := by
  obtain ⟨W, hW, g, hg, he⟩ := h
  refine ⟨Scheme.coverOfIsIso (𝟙 X), ?_⟩
  intro a
  refine ⟨inferInstance, W, hW, g, hg, ?_⟩
  change g ≫ W.ι = 𝟙 X ≫ f
  simpa only [Category.id_comp] using he

private theorem finite_product_charts {U V : Scheme.{u}} [QuasiSeparatedSpace U]
    (b : U ⟶ V) (D : Scheme.Cover.{u} Scheme.proetalePrecoverage U)
    (hD : ∀ a : D.I₀, IsAffine (D.X a))
    (hsource : ∀ a : D.I₀, ∃ (A : Scheme.{u}) (i : A ⟶ U) (r : D.X a ⟶ A),
      IsAffine A ∧ IsOpenImmersion i ∧ proAffineEtale r ∧ r ≫ i = D.f a)
    (htarget : ∀ a : D.I₀, ∃ (W : V.Opens) (_hW : IsAffineOpen W)
      (g : D.X a ⟶ W.toScheme), proAffineEtale g ∧ g ≫ W.ι = D.f a ≫ b)
    (n : ℕ) (a : Fin (n + 1) → D.I₀) :
    CompactSpace (∏ᶜ fun j : Fin (n + 1) ↦ Over.mk (D.f (a j))).left ∧
    QuasiSeparatedSpace (∏ᶜ fun j : Fin (n + 1) ↦ Over.mk (D.f (a j))).left ∧
    AffineIndEtaleCharts
      ((∏ᶜ fun j : Fin (n + 1) ↦ Over.mk (D.f (a j))).hom ≫ b) := by
  have transfer (X Y : Over U) (e : X ≅ Y)
      (hY : CompactSpace Y.left ∧ QuasiSeparatedSpace Y.left ∧
        AffineIndEtaleCharts (Y.hom ≫ b)) :
      CompactSpace X.left ∧ QuasiSeparatedSpace X.left ∧
        AffineIndEtaleCharts (X.hom ≫ b) := by
    have := hY.1
    have := hY.2.1
    refine ⟨QuasiCompact.compactSpace_of_compactSpace e.hom.left,
      quasiSeparatedSpace_of_quasiSeparated e.hom.left, ?_⟩
    have he : X.hom ≫ b = e.hom.left ≫ (Y.hom ≫ b) := by rw [← Category.assoc, e.hom.w]
    rw [he]
    exact charts_of_iso ((Over.forget U).mapIso e) (Y.hom ≫ b) hY.2.2
  induction n with
  | zero =>
    let W : Fin 1 → Over U := fun j ↦ Over.mk (D.f (a j))
    have : IsAffine (W default).left := hD (a default)
    exact transfer _ _ (productUniqueIso W)
      ⟨inferInstance, inferInstance, charts_of_affine _ (htarget (a default))⟩
  | succ n ih =>
    let W : Fin (n + 1 + 1) → Over U := fun j ↦ Over.mk (D.f (a j))
    let W' : Fin (n + 1) → Over U := fun j ↦ W j.succ
    have htail := ih (fun j ↦ a j.succ)
    have hP : CompactSpace (∏ᶜ W').left := htail.1
    have hP' : QuasiSeparatedSpace (∏ᶜ W').left := htail.2.1
    obtain ⟨A, i, r, hA, hi, hr, he⟩ := hsource (a 0)
    have hD₀ := hD (a 0)
    let c := pullback.cone (W 0).hom (∏ᶜ W').hom
    let bin := pullbackConeEquivBinaryFan.functor.obj c
    have hbin := IsLimit.pullbackConeEquivBinaryFanFunctor
      (pullback.isLimit (W 0).hom (∏ᶜ W').hom)
    let e := (limit.isLimit (Discrete.functor W)).conePointUniqueUpToIso
      (extendFanIsLimit W (productIsProduct W') hbin)
    apply transfer _ _ e
    change CompactSpace (pullback (D.f (a 0)) (∏ᶜ W').hom : Scheme.{u}) ∧
      QuasiSeparatedSpace (pullback (D.f (a 0)) (∏ᶜ W').hom : Scheme.{u}) ∧
      AffineIndEtaleCharts
        (pullback.fst (D.f (a 0)) (∏ᶜ W').hom ≫ D.f (a 0) ≫ b)
    refine ⟨inferInstance, ?_, ?_⟩
    · exact quasiSeparatedSpace_of_quasiSeparated
        (pullback.snd (D.f (a 0)) (∏ᶜ W').hom)
    · obtain ⟨T, hT⟩ := htail.2.2
      have h := exists_affine_indEtale_pullback_charts b (∏ᶜ W').hom i r hr T hT
      rw [he] at h
      have hsym := charts_of_iso (pullbackSymmetry (D.f (a 0)) (∏ᶜ W').hom)
        (pullback.fst (∏ᶜ W').hom (D.f (a 0)) ≫ (∏ᶜ W').hom ≫ b) h
      rw [pullback.condition_assoc]
      simpa only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc] using hsym

/-- Čech terms of a finite affine refinement have finite affine pro-étale charts.

Source: Bhatt--Scholze, Proposition 2.3.3(4), Theorem 2.3.4 and Remark 4.1.3
(blueprint: lem-sfb-weakly-etale-indetale-cech-refinement).

Proof: induct on the tuple length. Base change and composition preserve weak
étaleness and pro-affine-étaleness. For the induction step, refine an affine chart
of the previous product inside the inverse image of the selected affine source open,
then pull it back along the new affine pro-étale factor. The resulting affine charts
cover the fibre product. The qcqs pullback instances give quasi-compactness and
quasi-separatedness at each step. Quasi-compactness gives a finite subcover. All
pro-affine-étale presentations already use the prescribed small universe.
-/
private theorem finite_affine_cech_charts
    {U V : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [QuasiCompact b] [QuasiSeparated b] [WeaklyEtale b]
    (D : Scheme.Cover.{u} Scheme.proetalePrecoverage U)
    (_hfin : Finite D.I₀) (hD : ∀ a : D.I₀, IsAffine (D.X a))
    (hsource : ∀ a : D.I₀, ∃ (A : Scheme.{u}) (i : A ⟶ U) (r : D.X a ⟶ A),
      IsAffine A ∧ IsOpenImmersion i ∧ proAffineEtale r ∧ r ≫ i = D.f a)
    (htarget : ∀ a : D.I₀, ∃ (W : V.Opens) (_hW : IsAffineOpen W)
      (g : D.X a ⟶ W.toScheme), proAffineEtale g ∧ g ≫ W.ι = D.f a ≫ b) :
    ∀ (n : ℕ) (a : Fin (n + 1) → D.I₀),
      CompactSpace (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left ∧
      QuasiSeparatedSpace (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left ∧
      ∃ T : Scheme.OpenCover.{u}
          (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left,
        Finite T.I₀ ∧ ∀ β : T.I₀,
          IsAffine (T.X β) ∧
          ∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : T.X β ⟶ W.toScheme),
            proAffineEtale g ∧
            g ≫ W.ι = T.f β ≫
              (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).hom ≫ b := by
  intro n a
  obtain ⟨hqc, hqs, T, hT⟩ := finite_product_charts b D hD hsource htarget n a
  have := hqc
  refine ⟨hqc, hqs, T.finiteSubcover, inferInstance, ?_⟩
  intro β
  change IsAffine (T.X (T.idx β.val)) ∧ _
  exact hT (T.idx β.val)

/-- A qcqs weakly étale morphism admits a finite affine ind-étale Čech refinement.

Source: Bhatt--Scholze, Theorem 2.3.4, Proposition 2.3.3 and Remark 4.1.3
(blueprint: lem-sfb-weakly-etale-indetale-cech-refinement).
-/
theorem exists_finite_affine_indEtale_cech_refinement
    {U V : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [QuasiCompact b] [QuasiSeparated b] [WeaklyEtale b] :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U,
      Finite D.I₀ ∧ (∀ a : D.I₀, IsAffine (D.X a)) ∧
      ∀ (n : ℕ) (a : Fin (n + 1) → D.I₀),
        CompactSpace (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left ∧
        QuasiSeparatedSpace (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left ∧
        ∃ T : Scheme.OpenCover.{u}
            (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left,
          Finite T.I₀ ∧ ∀ β : T.I₀,
            IsAffine (T.X β) ∧
            ∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : T.X β ⟶ W.toScheme),
              proAffineEtale g ∧
              g ≫ W.ι = T.f β ≫
                (∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).hom ≫ b := by
  obtain ⟨D, hfin, hD, hsource, htarget⟩ := exists_finite_affine_indEtale_cover b
  refine ⟨D, hfin, hD, ?_⟩
  exact finite_affine_cech_charts b D hfin hD hsource htarget

end AlgebraicGeometry
