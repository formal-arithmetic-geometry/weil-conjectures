/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap
public import WeilConjectures.FourierTransform.ArtinSchreier
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Comparison with the prime-field Artin–Schreier character sheaf

Source: Laumon, Transformation de Fourier (1987), (0.2), (1.1.3), (1.1.3.6),
pp. 135 and 139–140; the explicit trace-polynomial comparison in the DAG proof
(blueprint: lem-a1-artin-schreier-prime-character-comparison).

The auxiliary definitions specialize the existing character projectors and function sheaf
with the canonical invertibility instance in characteristic zero. The base-change arrow is
pullback of sections, expressed as an arrow into a direct image. This adjoint formulation
records the naturality square without choosing identifications of images under pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

noncomputable section

variable {L : Type (u + 1)} [Field L] [CharZero L]

/-- The degree-q character projector on the explicit cover, using the upstream projector.
Source: Laumon (1.1.3), pp. 139–140
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonQIdempotent {k : Type u} [Field k] [Fintype k]
    {p r : ℕ} [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {f : Γ(X, ⊤)}
    (M : ArtinSchreierTraceMaps k p r b X f) (ψ : AddChar k L) :=
  letI : Invertible (Fintype.card k : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  isotypicIdempotent (artinSchreierFunctionProjection X (p ^ r) f)
    (fun c ↦ (M.σ c).hom) M.σ_over ψ

/-- The prime-degree projector for the function bf and the character of the prime field.
Source: Laumon (1.1.3), pp. 139–140
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonPIdempotent {k : Type u} [Field k]
    {p r : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {f : Γ(X, ⊤)}
    (M : ArtinSchreierTraceMaps k p r b X f) (Ψ : AddChar (ZMod p) L) :=
  letI : Invertible (Fintype.card (ZMod p) : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  isotypicIdempotent
    (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
    (fun d ↦ (M.τ d).hom) M.τ_over Ψ

/-- The existing function Artin–Schreier sheaf with characteristic-zero invertibility.
Source: Laumon (1.1.3.6), p. 140; def-fd-artin-schreier-sheaf
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonSheafOf {k : Type u} [Field k] [Fintype k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (ψ : AddChar k L) (f : Γ(X, ⊤)) :=
  letI : Invertible (Fintype.card k : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  artinSchreierSheafOf X ψ f

/-- The canonical arrow on pushed-forward constant sheaves associated to a map of covers
above h. Its adjoint is finite base change followed by the constant-sheaf unit isomorphism.
Source: finite exchange in the DAG proof of Laumon (1.1.3.6), p. 140
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonBaseMap {X X' Y Y' : Scheme.{u}}
    (π : Y ⟶ X) (π' : Y' ⟶ X') (h : X' ⟶ X) (a : Y' ⟶ Y)
    (ha : a ≫ π = π' ≫ h) :
    (π)_*[ModuleCat L].obj (𝟙_ _) ⟶ (h)_*[ModuleCat L].obj
      ((π')_*[ModuleCat L].obj (𝟙_ _)) :=
  lowerStarConstantSheafMapOfOver π (π' ≫ h) a ha ≫
    (lowerStarComp (ModuleCat L) π' h (π' ≫ h) rfl).inv.app (𝟙_ _)

private def comparisonToLine {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (f : Γ(X, ⊤)) :
    artinSchreierFunctionCover X n f ⟶ 𝔸(PUnit; Spec (.of K)) :=
  pullback.fst (AffineSpace.artinSchreierMap PUnit X n)
    (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f)) ≫ AffineSpace.map PUnit h

private lemma comparisonToLine_coord {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (f : Γ(X, ⊤)) :
    (comparisonToLine h n f).appTop (AffineSpace.coord _ PUnit.unit) =
      artinSchreierFunctionRoot X n f := by
  simp only [comparisonToLine, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.map_appTop_coord, artinSchreierFunctionRoot]
  rfl

private lemma comparisonToLine_over {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (f : Γ(X, ⊤)) :
    comparisonToLine h n f ≫ 𝔸(PUnit; Spec (.of K)) ↘ Spec (.of K) =
      artinSchreierFunctionProjection X n f ≫ h := by
  simp only [comparisonToLine, Category.assoc, AffineSpace.map_over]
  rw [← Category.assoc, ← AffineSpace.artinSchreierMap_over PUnit X n,
    pullback.condition_assoc]
  simp only [AffineSpace.homOfVector_over, Category.comp_id]
  rfl

private lemma comparisonToLine_isPullback {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (f : Γ(X, ⊤)) :
    IsPullback (comparisonToLine h n f) (artinSchreierFunctionProjection X n f)
      (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) n)
      (AffineSpace.homOfVector h (fun _ : PUnit ↦ f)) := by
  have hs := (IsPullback.of_hasPullback (AffineSpace.artinSchreierMap PUnit X n)
    (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f))).paste_horiz
      (AffineSpace.isPullback_map_artinSchreierMap h n)
  simpa only [comparisonToLine, artinSchreierFunctionProjection,
    AffineSpace.homOfVector_comp_map, Category.id_comp] using hs

private lemma comparisonToLine_translation {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (f : Γ(X, ⊤))
    (τ : artinSchreierFunctionCover X n f ⟶ artinSchreierFunctionCover X n f)
    (hτ : τ ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f) (c : K)
    (hc : τ.appTop (artinSchreierFunctionRoot X n f) =
      artinSchreierFunctionRoot X n f + (artinSchreierFunctionProjection X n f).appTop
        (h.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) :
    τ ≫ comparisonToLine h n f = comparisonToLine h n f ≫ artinSchreierTranslation K c := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, comparisonToLine_over, artinSchreierTranslation,
      AffineSpace.translation_over]
    rw [← Category.assoc, hτ]
  · intro i
    cases i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, comparisonToLine_coord,
      artinSchreierTranslation_appTop_coord, map_add, hc]
    congr 1
    have hb := congrArg (fun a ↦ a.appTop ((Scheme.ΓSpecIso (.of K)).inv c))
      (comparisonToLine_over h n f)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hb.symm

private lemma comparison_cover_transitive {K : Type u} [Field K] [Fintype K]
    {G : Type*} [AddCommGroup G] (α : G ≃+ K) {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (hn : n = Fintype.card K) (f : Γ(X, ⊤))
    (τ : G → (artinSchreierFunctionCover X n f ⟶ artinSchreierFunctionCover X n f))
    (hτ : ∀ g, τ g ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f)
    (hc : ∀ g, τ g ≫ comparisonToLine h n f =
      comparisonToLine h n f ≫ artinSchreierTranslation K (α g))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s t : Spec (.of Ω) ⟶ artinSchreierFunctionCover X n f)
    (hst : s ≫ artinSchreierFunctionProjection X n f =
      t ≫ artinSchreierFunctionProjection X n f) : ∃ g, s = t ≫ τ g := by
  have H := comparisonToLine_isPullback h n f
  obtain ⟨c, he⟩ := exists_eq_comp_artinSchreierTranslation
    (t ≫ comparisonToLine h n f) (s ≫ comparisonToLine h n f) (by
      simp only [Category.assoc, ← hn, H.w]
      rw [← Category.assoc, ← Category.assoc, hst])
  refine ⟨α.symm c, H.hom_ext ?_ ?_⟩
  · simpa only [Category.assoc, hc, AddEquiv.apply_symm_apply] using he
  · simpa only [Category.assoc, hτ] using hst

private def comparisonSheafMap {K : Type u} [Field K] [Fintype K]
    [Invertible (Fintype.card K : L)] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (hn : n = Fintype.card K)
    (f : Γ(X, ⊤)) (χ : AddChar K L) :=
  artinSchreierSheafUpperStarToLowerStar (artinSchreierFunctionProjection X n f)
    (AffineSpace.homOfVector h (fun _ : PUnit ↦ f)) (comparisonToLine h n f)
    (by simpa only [hn] using (comparisonToLine_isPullback h n f).w) χ

omit [CharZero L] in
private lemma comparisonSheafMap_isIso {K : Type u} [Field K] [Fintype K]
    [Invertible (Fintype.card K : L)] {G : Type*} [AddCommGroup G] [Fintype G]
    [Invertible (Fintype.card G : L)] (α : G ≃+ K) {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (n : ℕ) (hn : n = Fintype.card K) (f : Γ(X, ⊤))
    (τ : G → (artinSchreierFunctionCover X n f ⟶ artinSchreierFunctionCover X n f))
    (hτ : ∀ g, τ g ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f) [∀ g, IsFinite (τ g)]
    (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b)
    (hc : ∀ g, τ g ≫ comparisonToLine h n f =
      comparisonToLine h n f ≫ artinSchreierTranslation K (α g))
    (χ : AddChar G L) (χK : AddChar K L) (hχ : ∀ g, χK (α g) = χ g) :
    IsIso (comparisonSheafMap h n hn f χK ≫
      factorThruImage (isotypicIdempotent (artinSchreierFunctionProjection X n f) τ hτ χ)) := by
  have H := comparisonToLine_isPullback h n f
  have hfinite : IsFinite (artinSchreierFunctionProjection X n f) :=
    MorphismProperty.of_isPullback H (by
      simpa only [hn] using (inferInstance : IsFinite
        (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) (Fintype.card K))))
  have hsurj : Surjective (artinSchreierFunctionProjection X n f) :=
    MorphismProperty.of_isPullback H (by
      simpa only [hn] using (show Surjective
        (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) (Fintype.card K)) from
          ⟨AffineSpace.surjective_artinSchreierMap K⟩))
  have hiso := isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent
    (artinSchreierFunctionProjection X n f) τ hτ χ hadd
    (comparison_cover_transitive α h n hn f τ hτ hc)
    (comparisonSheafMap h n hn f χK) (fun g ↦ by
      simpa only [comparisonSheafMap, hχ] using
        artinSchreierSheafUpperStarToLowerStar_comp
          (artinSchreierFunctionProjection X n f)
          (AffineSpace.homOfVector h (fun _ : PUnit ↦ f)) (comparisonToLine h n f)
          (by simpa only [hn] using H.w) χK (τ g) (hτ g) (α g) (hc g))
    (isIso_upperStar_map_artinSchreierSheafUpperStarToLowerStar_comp_counit _ _ _ _ _)
  have := reflectsIsomorphisms_upperStar_of_surjective L
    (artinSchreierFunctionProjection X n f) hsurj.1
  exact isIso_of_reflects_iso _ (artinSchreierFunctionProjection X n f)^*[ModuleCat L]

omit [CharZero L] in
private lemma comparisonBaseMap_naturality
    {X X' A B A' B' : Scheme.{u}} (πA : A ⟶ X) (πB : B ⟶ X)
    (πA' : A' ⟶ X') (πB' : B' ⟶ X') (h : X' ⟶ X)
    (θ : B ⟶ A) (hθ : θ ≫ πA = πB)
    (θ' : B' ⟶ A') (hθ' : θ' ≫ πA' = πB')
    (a : A' ⟶ A) (ha : a ≫ πA = πA' ≫ h)
    (b : B' ⟶ B) (hb : b ≫ πB = πB' ≫ h)
    (hw : θ' ≫ a = b ≫ θ) :
    lowerStarConstantSheafMapOfOver (Λ := L) πA πB θ hθ ≫
        artinSchreierComparisonBaseMap πB πB' h b hb =
      artinSchreierComparisonBaseMap πA πA' h a ha ≫
        (h)_*[ModuleCat L].map (lowerStarConstantSheafMapOfOver πA' πB' θ' hθ') := by
  rw [← cancel_mono ((lowerStarComp (ModuleCat L) πB' h (πB' ≫ h) rfl).hom.app (𝟙_ _))]
  simp only [artinSchreierComparisonBaseMap, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [lowerStar_map_lowerStarConstantSheafMapOfOver]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← lowerStarConstantSheafMapOfOver_comp, ← lowerStarConstantSheafMapOfOver_comp]
  exact lowerStarConstantSheafMapOfOver_congr _ _ hw.symm _ _

omit [CharZero L] in
private lemma comparisonBaseMap_projector
    {G : Type*} [AddCommGroup G] [Fintype G] [Invertible (Fintype.card G : L)]
    {X X' Y Y' : Scheme.{u}} (π : Y ⟶ X) (π' : Y' ⟶ X') (h : X' ⟶ X)
    (a : Y' ⟶ Y) (ha : a ≫ π = π' ≫ h)
    (τ : G → (Y ⟶ Y)) (hτ : ∀ g, τ g ≫ π = π)
    (τ' : G → (Y' ⟶ Y')) (hτ' : ∀ g, τ' g ≫ π' = π')
    (hw : ∀ g, τ' g ≫ a = a ≫ τ g) (χ : AddChar G L) :
    isotypicIdempotent π τ hτ χ ≫ artinSchreierComparisonBaseMap π π' h a ha =
      artinSchreierComparisonBaseMap π π' h a ha ≫
        (h)_*[ModuleCat L].map (isotypicIdempotent π' τ' hτ' χ) := by
  simp only [isotypicIdempotent, Preadditive.sum_comp, Functor.map_sum,
    Preadditive.comp_sum, Linear.smul_comp, Functor.map_smul, Linear.comp_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  simp only [lowerStarConstantSheafEndOfOver_eq_mapOfOver]
  exact comparisonBaseMap_naturality π π π' π' h (τ g) (hτ g) (τ' g) (hτ' g)
    a ha a ha (hw g)

private lemma image_comparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : D ⥤ C) {A B : C} {A' B' : D}
    (P : A ⟶ A) (Q : B ⟶ B) (P' : A' ⟶ A') (Q' : B' ⟶ B')
    (hP : P ≫ P = P) (φ : A ⟶ B) (φ' : A' ⟶ B')
    (βA : A ⟶ F.obj A') (βB : B ⟶ F.obj B')
    (e : image P ≅ image Q) (e' : image P' ≅ image Q')
    (he : e.hom ≫ image.ι Q = image.ι P ≫ φ)
    (he' : e'.hom ≫ image.ι Q' = image.ι P' ≫ φ')
    (hprojector : P ≫ βA = βA ≫ F.map P')
    (hsquare : φ ≫ βB = βA ≫ F.map φ') :
    image.ι P ≫ βA ≫ F.map (factorThruImage P') ≫
        F.map e'.hom ≫ F.map (image.ι Q') =
      e.hom ≫ image.ι Q ≫ βB := by
  have hι : image.ι P ≫ P = image.ι P := by
    rw [← cancel_epi (factorThruImage P), image.fac_assoc, image.fac, hP]
  calc
    _ = image.ι P ≫ βA ≫ F.map (factorThruImage P' ≫ e'.hom ≫ image.ι Q') := by
      simp only [Functor.map_comp]
    _ = image.ι P ≫ βA ≫ F.map (P' ≫ φ') := by
      rw [he', image.fac_assoc]
    _ = image.ι P ≫ (βA ≫ F.map P') ≫ F.map φ' := by
      simp only [Functor.map_comp, Category.assoc]
    _ = image.ι P ≫ (P ≫ βA) ≫ F.map φ' := by rw [← hprojector]
    _ = image.ι P ≫ βA ≫ F.map φ' := by simp only [← Category.assoc, hι]
    _ = image.ι P ≫ (φ ≫ βB) := by rw [← hsquare]
    _ = e.hom ≫ image.ι Q ≫ βB := by
      simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ βB) he.symm

omit [CharZero L] in
private lemma isIso_eval_isotypic
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π]
    {G : Type*} [AddCommGroup G] [Fintype G]
    (τ : G → (Y ⟶ Y)) (hτ : ∀ g, τ g ≫ π = π) [∀ g, IsFinite (τ g)]
    [Invertible (Fintype.card G : L)] (χ : AddChar G L)
    (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b) (hzero : τ 0 = 𝟙 _)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (s : Scheme.Hom.GeometricFiber π x)
    (htrans : ∀ t : Scheme.Hom.GeometricFiber π x, ∃ g, s.1 = t.1 ≫ τ g)
    (hfree : ∀ g, s.1 ≫ τ g = s.1 → g = 0) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map
        (image.ι (isotypicIdempotent π τ hτ χ)) ≫
      stalkRestrict (ModuleCat.{u + 1} L) π x s (𝟙_ _)) := by
  classical
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} L) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have := (Scheme.pointSmallEtale x).sheafFiber_additive (A := ModuleCat.{u + 1} L)
  let ρ := fun t : Scheme.Hom.GeometricFiber π x ↦
    stalkRestrict (ModuleCat.{u + 1} L) π x t (𝟙_ _)
  let ι := image.ι (isotypicIdempotent π τ hτ χ)
  let r := factorThruImage (isotypicIdempotent π τ hτ χ)
  have hmono : Mono ((Scheme.pointSmallEtale x).sheafFiber.map ι ≫ ρ s) :=
    mono_sheafFiber_map_image_ι_isotypicIdempotent_comp_stalkRestrict
      π τ hτ χ hadd x s htrans
  have hepi : IsSplitEpi ((Scheme.pointSmallEtale x).sheafFiber.map ι ≫ ρ s) := by
    let j : (Scheme.pointSmallEtale s.1).sheafFiber.obj
        (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} L))) ⟶
        (Scheme.pointSmallEtale x).sheafFiber.obj ((π)_*[ModuleCat L].obj (𝟙_ _)) :=
      Pi.lift (fun t ↦ if h : t = s then eqToHom (by rw [h]) else 0) ≫ inv (Pi.lift ρ)
    have hj (t) : j ≫ ρ t = if h : t = s then eqToHom (by rw [h]) else 0 := by
      have : inv (Pi.lift ρ) ≫ ρ t = Pi.π _ t := by
        rw [IsIso.inv_comp_eq, Pi.lift_π]
      simp only [j, Category.assoc]
      rw [this, Pi.lift_π]
    refine ⟨⟨(Fintype.card G : L) • (j ≫ (Scheme.pointSmallEtale x).sheafFiber.map r), ?_⟩⟩
    rw [Linear.smul_comp, Category.assoc,
      ← Category.assoc ((Scheme.pointSmallEtale x).sheafFiber.map r),
      ← CategoryTheory.Functor.map_comp, image.fac, isotypicIdempotent, Functor.map_sum]
    simp only [GrothendieckTopology.Point.sheafFiber_map_smul, Preadditive.sum_comp,
      Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
    rw [Finset.sum_eq_single (0 : G)]
    · rw [lowerStarConstantSheafEndOfOver_of_eq_id π (τ 0) hzero,
        CategoryTheory.Functor.map_id, Category.id_comp]
      erw [hj s]
      rw [dif_pos rfl, eqToHom_refl, neg_zero, AddChar.map_zero_eq_one, mul_one,
        smul_smul, mul_invOf_self, one_smul]
    · intro g _ hg
      obtain ⟨θ, hθ⟩ :=
        exists_sheafFiber_map_lowerStarConstantSheafEndOfOver_comp_stalkRestrict
          (Λ := L) π τ hτ x g s
          ⟨s.1 ≫ τ g, by rw [Category.assoc, hτ, s.2]⟩ rfl
      have hne : (⟨s.1 ≫ τ g, by rw [Category.assoc, hτ, s.2]⟩ :
          Scheme.Hom.GeometricFiber π x) ≠ s := fun h ↦
        hg (hfree g (congrArg Subtype.val h))
      erw [hθ, ← Category.assoc, hj, dif_neg hne]
      rw [zero_comp, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact isIso_of_mono_of_isSplitEpi _

omit [CharZero L] in
private lemma comparison_eval_isIso {K : Type u} [Field K] [Fintype K]
    {G : Type*} [AddCommGroup G] [Fintype G] [Invertible (Fintype.card G : L)]
    (α : G ≃+ K) {X : Scheme.{u}} (h : X ⟶ Spec (.of K))
    (n : ℕ) (hn : n = Fintype.card K) (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X n f)]
    (τ : G → (artinSchreierFunctionCover X n f ⟶ artinSchreierFunctionCover X n f))
    (hτ : ∀ g, τ g ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f) [∀ g, IsFinite (τ g)]
    (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b) (hzero : τ 0 = 𝟙 _)
    (hc : ∀ g, τ g ≫ comparisonToLine h n f =
      comparisonToLine h n f ≫ artinSchreierTranslation K (α g))
    (χ : AddChar G L) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (s : Scheme.Hom.GeometricFiber
      (artinSchreierFunctionProjection X n f) x) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map
        (image.ι (isotypicIdempotent (artinSchreierFunctionProjection X n f) τ hτ χ)) ≫
      stalkRestrict (ModuleCat L) (artinSchreierFunctionProjection X n f) x s (𝟙_ _)) := by
  apply isIso_eval_isotypic _ τ hτ χ hadd hzero x s
  · intro t
    exact comparison_cover_transitive α h n hn f τ hτ hc Ω s.1 t.1 (by rw [s.2, t.2])
  · intro g hg
    apply α.injective
    rw [map_zero]
    apply eq_zero_of_comp_artinSchreierTranslation_eq (s.1 ≫ comparisonToLine h n f)
    have he := congrArg (fun a ↦ a ≫ comparisonToLine h n f) hg
    simpa only [Category.assoc, hc] using he

omit [CharZero L] in
private lemma comparisonMap_stalk {X A B : Scheme.{u}}
    (πA : A ⟶ X) (πB : B ⟶ X) (θ : B ⟶ A) (hθ : θ ≫ πA = πB)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (s : Scheme.Hom.GeometricFiber πB x) :
    (Scheme.pointSmallEtale x).sheafFiber.map
        (lowerStarConstantSheafMapOfOver (Λ := L) πA πB θ hθ) ≫
      stalkRestrict (ModuleCat L) πB x s (𝟙_ _) =
    stalkRestrict (ModuleCat L) πA x
        ⟨s.1 ≫ θ, by rw [Category.assoc, hθ, s.2]⟩ (𝟙_ _) ≫
      (Scheme.pointSmallEtale (s.1 ≫ θ)).sheafFiber.map
        (Functor.LaxMonoidal.ε (θ)_*[ModuleCat L]) ≫
      stalkRestrict (ModuleCat L) θ (s.1 ≫ θ) ⟨s.1, rfl⟩ (𝟙_ _) := by
  rw [lowerStarConstantSheafMapOfOver, Functor.map_comp, Category.assoc,
    sheafFiber_map_lowerStarComp_hom_app_stalkRestrict,
    ← Category.assoc, ← stalkRestrict_naturality, Category.assoc]

private def comparisonPrimeBase {k : Type u} [Field k] (p : ℕ)
    [Algebra (ZMod p) k] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    X ⟶ Spec (.of (ULift.{u} (ZMod p))) :=
  (X ↘ Spec (.of k)) ≫ Scheme.Spec.map
    (CommRingCat.ofHom ((algebraMap (ZMod p) k).comp
      ULift.ringEquiv.toRingHom)).op

private lemma comparisonPrimeBase_constant {k : Type u} [Field k] (p : ℕ)
    [Algebra (ZMod p) k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (d : ZMod p) :
    (comparisonPrimeBase (k := k) p X).appTop
        ((Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv (ULift.up d)) =
      artinSchreierBaseConstants k X (algebraMap (ZMod p) k d) := by
  have h := congrArg (fun a : CommRingCat.of (ULift.{u} (ZMod p)) ⟶
      Γ(Spec (.of k), ⊤) ↦ a (ULift.up d))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      ((algebraMap (ZMod p) k).comp ULift.ringEquiv.toRingHom)))
  change (Scheme.ΓSpecIso (.of k)).inv (algebraMap (ZMod p) k d) =
    (Scheme.Spec.map (CommRingCat.ofHom ((algebraMap (ZMod p) k).comp
      ULift.ringEquiv.toRingHom)).op).appTop
      ((Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv (ULift.up d)) at h
  exact congrArg (fun x ↦ (X ↘ Spec (.of k)).appTop x) h.symm

private lemma comparison_q_translation {k : Type u} [Field k] {p r : ℕ}
    [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {f : Γ(X, ⊤)} (M : ArtinSchreierTraceMaps k p r b X f) (c : k) :
    (M.σ c).hom ≫ comparisonToLine (X ↘ Spec (.of k)) (p ^ r) f =
      comparisonToLine (X ↘ Spec (.of k)) (p ^ r) f ≫ artinSchreierTranslation k c :=
  comparisonToLine_translation _ _ _ _ (M.σ_over c) c (M.σ_root c)

private lemma comparison_p_translation {k : Type u} [Field k] {p r : ℕ}
    [Fact p.Prime] [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {f : Γ(X, ⊤)}
    (M : ArtinSchreierTraceMaps k p r b X f) (d : ZMod p) :
    (M.τ d).hom ≫ comparisonToLine (comparisonPrimeBase (k := k) p X) p
        (artinSchreierBaseConstants k X b * f) =
      comparisonToLine (comparisonPrimeBase (k := k) p X) p
        (artinSchreierBaseConstants k X b * f) ≫
        artinSchreierTranslation (ULift.{u} (ZMod p)) (ULift.up d) := by
  apply comparisonToLine_translation _ _ _ _ (M.τ_over d) (ULift.up d)
  rw [comparisonPrimeBase_constant]
  exact M.τ_root d

omit [CharZero L] in
private lemma comparison_eigenmap_comp
    {C : Type*} [Category C] [Preadditive C] [Linear L C]
    {A B T : C} (ι : T ⟶ A) (φ : A ⟶ B) (σ : A ⟶ A) (τ : B ⟶ B)
    (a : L) (hw : φ ≫ τ = σ ≫ φ) (hι : ι ≫ σ = a • ι) :
    (ι ≫ φ) ≫ τ = a • (ι ≫ φ) := by
  calc
    (ι ≫ φ) ≫ τ = ι ≫ (φ ≫ τ) := Category.assoc _ _ _
    _ = ι ≫ (σ ≫ φ) := congrArg (fun t ↦ ι ≫ t) hw
    _ = (ι ≫ σ) ≫ φ := (Category.assoc _ _ _).symm
    _ = (a • ι) ≫ φ := congrArg (fun t ↦ t ≫ φ) hι
    _ = a • (ι ≫ φ) := Linear.smul_comp _ _ _ a ι φ

attribute [local irreducible] artinSchreierFunctionCover
  artinSchreierFunctionProjection artinSchreierBaseConstants

set_option maxHeartbeats 800000 in
-- Comparing projector images elaborates several dependent sheaf functors.
set_option backward.isDefEq.respectTransparency true in
private lemma comparison_fixed_images {k : Type u} [Field k] [Fintype k]
    {p r : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {f : Γ(X, ⊤)}
    (M : ArtinSchreierTraceMaps k p r b X f) (hcard : Fintype.card k = p ^ r)
    (Ψ : AddChar (ZMod p) L) (ψ : AddChar k L)
    (hb : ∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k (b * c)))
    (hequiv : ∀ c : k, (M.σ c).hom ≫ M.θ =
      M.θ ≫ (M.τ (Algebra.trace (ZMod p) k (b * c))).hom) :
    ∃ e : image (artinSchreierComparisonPIdempotent M Ψ) ≅
        image (artinSchreierComparisonQIdempotent M ψ),
      e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) =
        image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
          lowerStarConstantSheafMapOfOver
            (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
            (artinSchreierFunctionProjection X (p ^ r) f) M.θ M.θ_over ∧
      Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonQIdempotent M ψ)) ∧
      Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonPIdempotent M Ψ)) ∧
      Nonempty (artinSchreierComparisonSheafOf X ψ f ≅
        image (artinSchreierComparisonQIdempotent M ψ)) := by
  let : Invertible (Fintype.card k : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let : Invertible (Fintype.card (ZMod p) : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let πq := artinSchreierFunctionProjection X (p ^ r) f
  let πp := artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)
  have hn : p = Fintype.card (ULift.{u} (ZMod p)) := by simp
  have hfiniteq : IsFinite πq :=
    MorphismProperty.of_isPullback (comparisonToLine_isPullback
      (X ↘ Spec (.of k)) (p ^ r) f) (by
      simpa only [← hcard] using (inferInstance : IsFinite
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))))
  have hfinitep : IsFinite πp :=
    MorphismProperty.of_isPullback (comparisonToLine_isPullback
      (comparisonPrimeBase (k := k) p X) p (artinSchreierBaseConstants k X b * f)) (by
      simpa only [Fintype.card_ulift, ZMod.card] using (inferInstance : IsFinite
        (AffineSpace.artinSchreierMap PUnit (Spec (.of (ULift.{u} (ZMod p))))
          (Fintype.card (ULift.{u} (ZMod p))))))
  have hsurj : Surjective πq :=
    MorphismProperty.of_isPullback (comparisonToLine_isPullback
      (X ↘ Spec (.of k)) (p ^ r) f) (by
      simpa only [← hcard] using (show Surjective
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) from
          ⟨AffineSpace.surjective_artinSchreierMap k⟩))
  let P := artinSchreierComparisonPIdempotent M Ψ
  let Q := artinSchreierComparisonQIdempotent M ψ
  let θmap := lowerStarConstantSheafMapOfOver (Λ := L) πp πq M.θ M.θ_over
  let φ := image.ι P ≫ θmap
  have hφ : ∀ c : k, φ ≫ lowerStarConstantSheafEndOfOver πq (M.σ c).hom
      (M.σ_over c) = ψ c • φ := by
    intro c
    have hw : θmap ≫ lowerStarConstantSheafEndOfOver πq (M.σ c).hom (M.σ_over c) =
        lowerStarConstantSheafEndOfOver πp
          (M.τ (Algebra.trace (ZMod p) k (b * c))).hom (M.τ_over _) ≫ θmap := by
      simp only [θmap, lowerStarConstantSheafEndOfOver_eq_mapOfOver,
        ← lowerStarConstantSheafMapOfOver_comp]
      exact lowerStarConstantSheafMapOfOver_congr _ _ (hequiv c) _ _
    have hh := image_ι_isotypicIdempotent_comp πp (fun d ↦ (M.τ d).hom)
      M.τ_over Ψ M.τ_add (Algebra.trace (ZMod p) k (b * c))
    change image.ι P ≫ _ = Ψ (Algebra.trace (ZMod p) k (b * c)) • image.ι P at hh
    rw [← hb c] at hh
    exact comparison_eigenmap_comp (image.ι P) θmap _ _ (ψ c) hw hh
  have hiso : IsIso ((πq)^*[ModuleCat L].map φ ≫
      (upperStarLowerStarAdjunction (ModuleCat L) πq).counit.app (𝟙_ _)) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun z ↦ ?_
    rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
      ((Scheme.pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} L))]
    let s := (artinSchreierFunctionCover X (p ^ r) f).algClosurePoint z
    rw [sheafFiber_map_upperStar_map_comp_counit]
    change IsIso (_ ≫ (Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map φ ≫ _)
    have hp := comparison_eval_isIso
      (ULift.ringEquiv.symm.toAddEquiv : ZMod p ≃+ ULift.{u} (ZMod p))
      (comparisonPrimeBase (k := k) p X) p hn (artinSchreierBaseConstants k X b * f)
      (fun d ↦ (M.τ d).hom) M.τ_over M.τ_add M.τ_zero
      (comparison_p_translation M) Ψ (s ≫ πq)
      ⟨s ≫ M.θ, by rw [Category.assoc, M.θ_over]⟩
    have heval : (Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map φ ≫
        stalkRestrict (ModuleCat L) πq (s ≫ πq) ⟨s, rfl⟩ (𝟙_ _) =
      ((Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map (image.ι P) ≫
        stalkRestrict (ModuleCat L) πp (s ≫ πq)
          ⟨s ≫ M.θ, by rw [Category.assoc, M.θ_over]⟩ (𝟙_ _)) ≫
      ((Scheme.pointSmallEtale (s ≫ M.θ)).sheafFiber.map
        (Functor.LaxMonoidal.ε (M.θ)_*[ModuleCat L]) ≫
        stalkRestrict (ModuleCat L) M.θ (s ≫ M.θ) ⟨s, rfl⟩ (𝟙_ _)) := by
      exact (congrArg (fun t ↦ t ≫ stalkRestrict (ModuleCat L) πq
          (s ≫ πq) ⟨s, rfl⟩ (𝟙_ _))
          ((Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map_comp (image.ι P) θmap)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t ↦
              (Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map (image.ι P) ≫ t)
            (comparisonMap_stalk πp πq M.θ M.θ_over (s ≫ πq) ⟨s, rfl⟩)).trans
            (Category.assoc _ _ _).symm))
    have : IsIso ((Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map (image.ι P) ≫
        stalkRestrict (ModuleCat L) πp (s ≫ πq)
          ⟨s ≫ M.θ, by rw [Category.assoc, M.θ_over]⟩ (𝟙_ _)) := hp
    have hright : IsIso
        (((Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map (image.ι P) ≫
          stalkRestrict (ModuleCat L) πp (s ≫ πq)
            ⟨s ≫ M.θ, by rw [Category.assoc, M.θ_over]⟩ (𝟙_ _)) ≫
        ((Scheme.pointSmallEtale (s ≫ M.θ)).sheafFiber.map
          (Functor.LaxMonoidal.ε (M.θ)_*[ModuleCat L]) ≫
          stalkRestrict (ModuleCat L) M.θ (s ≫ M.θ) ⟨s, rfl⟩ (𝟙_ _))) := inferInstance
    have : IsIso ((Scheme.pointSmallEtale (s ≫ πq)).sheafFiber.map φ ≫
        stalkRestrict (ModuleCat L) πq (s ≫ πq) ⟨s, rfl⟩ (𝟙_ _)) :=
      heval.symm ▸ hright
    infer_instance
  have htrans := comparison_cover_transitive (AddEquiv.refl k)
    (X ↘ Spec (.of k)) (p ^ r) hcard.symm f (fun c ↦ (M.σ c).hom)
    M.σ_over (comparison_q_translation M)
  have hiso' := isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent
    πq (fun c ↦ (M.σ c).hom) M.σ_over ψ M.σ_add htrans φ hφ hiso
  have : IsIso ((πq)^*[ModuleCat L].map (φ ≫ factorThruImage Q)) := hiso'
  have := reflectsIsomorphisms_upperStar_of_surjective L πq hsurj.1
  have : IsIso (φ ≫ factorThruImage Q) :=
    isIso_of_reflects_iso _ (πq)^*[ModuleCat L]
  let e : image P ≅ image Q := asIso (φ ≫ factorThruImage Q)
  have he : e.hom ≫ image.ι Q = φ := by
    simp only [e, asIso_hom, Category.assoc, image.fac]
    exact comp_isotypicIdempotent πq (fun c ↦ (M.σ c).hom) M.σ_over ψ φ hφ
  have heq := comparisonSheafMap_isIso (AddEquiv.refl k)
    (X ↘ Spec (.of k)) (p ^ r) hcard.symm f (fun c ↦ (M.σ c).hom)
    M.σ_over M.σ_add (comparison_q_translation M) ψ ψ (fun _ ↦ rfl)
  have heq' : IsIso (comparisonSheafMap (X ↘ Spec (.of k)) (p ^ r) hcard.symm f ψ ≫
      factorThruImage Q) := heq
  let eq : artinSchreierComparisonSheafOf X ψ f ≅ image Q :=
    @asIso _ _ _ _
      (comparisonSheafMap (X ↘ Spec (.of k)) (p ^ r) hcard.symm f ψ ≫
        factorThruImage Q) heq'
  have : Scheme.IsLocallyConstantSheaf (artinSchreierComparisonSheafOf X ψ f) :=
    inferInstanceAs (Scheme.IsLocallyConstantSheaf (artinSchreierSheafOf X ψ f))
  have : Scheme.IsLocallyConstantSheaf (image Q) := Scheme.IsLocallyConstantSheaf.of_iso eq
  exact ⟨e, he, inferInstance, Scheme.IsLocallyConstantSheaf.of_iso e.symm, ⟨eq⟩⟩

omit [CharZero L] in
/-- Character parametrization subresult for the prime-field comparison.
Source: Laumon (0.2), p. 135 (blueprint: lem-a1-artin-schreier-prime-character-comparison).
-/
private lemma exists_comparison_parameter (k : Type u) [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) L) (hΨ : Ψ ≠ 1) (ψ : AddChar k L) (hψ : ψ ≠ 1) :
    ∃ b : kˣ,
      (∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b : k) * c))) ∧
      (∀ b' : kˣ, (∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b' : k) * c))) →
        b' = b) := by
  classical
  let : Fintype k := Fintype.ofFinite k
  let χ : AddChar k L := Ψ.compAddMonoidHom (Algebra.trace (ZMod p) k).toAddMonoidHom
  have hχ : χ ≠ 1 := by
    intro h
    obtain ⟨c, ht⟩ : ∃ c : k, Algebra.trace (ZMod p) k c ≠ 0 := by
      have heq : ringChar k = p := ringChar.eq k p
      subst p
      simpa only [one_mul] using FiniteField.trace_to_zmod_nondegenerate k one_ne_zero
    apply ht
    apply (AddChar.IsPrimitive.of_ne_one hΨ).zmod_char_eq_one_iff p _ |>.mp
    exact DFunLike.congr_fun h c
  have hli : LinearIndependent L
      (fun φ : AddChar k L ↦ (φ.toMonoidHom : Multiplicative k → L)) :=
    (linearIndependent_monoidHom (Multiplicative k) L).comp
      AddChar.toMonoidHomEquiv AddChar.toMonoidHomEquiv.injective
  let : Finite (AddChar k L) := hli.finite
  let : Fintype (AddChar k L) := Fintype.ofFinite _
  have hle : Fintype.card (AddChar k L) ≤ Fintype.card k := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_multiplicative] using
      hli.fintype_card_le_finrank
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hχ)
  have hbij : Function.Bijective χ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, Nat.le_antisymm (Fintype.card_le_of_injective _ hinj) hle⟩
  obtain ⟨b, hb⟩ := hbij.surjective ψ
  have hb0 : b ≠ 0 := by
    intro h
    apply hψ
    simpa only [h, AddChar.mulShift_zero] using hb.symm
  refine ⟨Units.mk0 b hb0, ?_, ?_⟩
  · intro c
    exact (DFunLike.congr_fun hb c).symm
  · intro b' hb'
    apply Units.ext
    apply hinj
    apply AddChar.ext
    intro c
    exact (hb' c).symm.trans (DFunLike.congr_fun hb c).symm


set_option maxHeartbeats 800000 in
-- The naturality square elaborates dependent images and pushforward compositions.
set_option backward.isDefEq.respectTransparency true in
/-- Fixed-parameter geometric comparison subresult.
Source: Laumon (1.1.3), (1.1.3.6), pp. 139--140; explicit trace-polynomial comparison
(blueprint: lem-a1-artin-schreier-prime-character-comparison).
-/
private lemma comparison_geometric (k : Type u) [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hr : 1 ≤ r) (hcard : Fintype.card k = p ^ r)
    (Ψ : AddChar (ZMod p) L) (ψ : AddChar k L)
    (b : kˣ) (hb : ∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b : k) * c))) :
      ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
        [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
        [QuasiCompact (X ↘ Spec (.of k))] (f : Γ(X, ⊤)),
      ∃ (M : ArtinSchreierTraceMaps k p r (b : k) X f)
        (e : image (artinSchreierComparisonPIdempotent M Ψ) ≅
          image (artinSchreierComparisonQIdempotent M ψ)),
        e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) =
          image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
            lowerStarConstantSheafMapOfOver
              (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
              (artinSchreierFunctionProjection X (p ^ r) f) M.θ M.θ_over ∧
        Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonQIdempotent M ψ)) ∧
        Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonPIdempotent M Ψ)) ∧
        Nonempty (artinSchreierComparisonSheafOf X ψ f ≅
          image (artinSchreierComparisonQIdempotent M ψ)) ∧
        ∀ (X' : Scheme.{u}) [X'.Over (Spec (.of k))]
          [IsSeparated (X' ↘ Spec (.of k))] [LocallyOfFiniteType (X' ↘ Spec (.of k))]
          [QuasiCompact (X' ↘ Spec (.of k))] (h : X' ⟶ X) [h.IsOver (Spec (.of k))],
        ∃ (M' : ArtinSchreierTraceMaps k p r (b : k) X' (h.appTop f))
          (uq : artinSchreierFunctionCover X' (p ^ r) (h.appTop f) ⟶
            artinSchreierFunctionCover X (p ^ r) f)
          (up : artinSchreierFunctionCover X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ⟶
            artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f))
          (hq : IsPullback uq (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f))
            (artinSchreierFunctionProjection X (p ^ r) f) h)
          (hp : IsPullback up (artinSchreierFunctionProjection X' p
              (artinSchreierBaseConstants k X' b * h.appTop f))
            (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)) h)
          (e' : image (artinSchreierComparisonPIdempotent M' Ψ) ≅
            image (artinSchreierComparisonQIdempotent M' ψ)),
          uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
            artinSchreierFunctionRoot X' (p ^ r) (h.appTop f) ∧
          up.appTop (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
            artinSchreierFunctionRoot X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ∧
          e'.hom ≫ image.ι (artinSchreierComparisonQIdempotent M' ψ) =
            image.ι (artinSchreierComparisonPIdempotent M' Ψ) ≫
              lowerStarConstantSheafMapOfOver
                (artinSchreierFunctionProjection X' p
                  (artinSchreierBaseConstants k X' b * h.appTop f))
                (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f)) M'.θ M'.θ_over ∧
          image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
              artinSchreierComparisonBaseMap
                (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
                (artinSchreierFunctionProjection X' p
                  (artinSchreierBaseConstants k X' b * h.appTop f)) h up hp.w ≫
              (h)_*[ModuleCat L].map
                (factorThruImage (artinSchreierComparisonPIdempotent M' Ψ)) ≫
              (h)_*[ModuleCat L].map e'.hom ≫
              (h)_*[ModuleCat L].map (image.ι (artinSchreierComparisonQIdempotent M' ψ)) =
            e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) ≫
              artinSchreierComparisonBaseMap
                (artinSchreierFunctionProjection X (p ^ r) f)
                (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f)) h uq hq.w  := by
  intro X _ _ _ _ f
  have htrace := artinSchreier_trace_cover_map k p r hr hcard (b : k) b.ne_zero X f
  rcases htrace with ⟨M, _, _, _, _, _, hequiv, _, _, hbase⟩
  have hcomparison := comparison_fixed_images M hcard Ψ ψ hb hequiv
  rcases hcomparison with ⟨e, he, hlq, hlp, heq⟩
  refine ⟨M, e, he, hlq, hlp, heq, ?_⟩
  intro X' _ _ _ _ h _
  have hbase' := hbase X' h
  rcases hbase' with ⟨M', uq, up, hq, hp, hrootq, hrootp, hσ, hτ, hθ⟩
  have hequiv' (c : k) : (M'.σ c).hom ≫ M'.θ =
      M'.θ ≫ (M'.τ (Algebra.trace (ZMod p) k ((b : k) * c))).hom := by
    apply hp.hom_ext
    · calc
        _ = ((M'.σ c).hom ≫ uq) ≫ M.θ := by
          rw [Category.assoc, hθ, ← Category.assoc]
        _ = (uq ≫ (M.σ c).hom) ≫ M.θ := by rw [hσ]
        _ = uq ≫ M.θ ≫ (M.τ _).hom := by rw [Category.assoc, hequiv]
        _ = (M'.θ ≫ up) ≫ (M.τ _).hom := by rw [hθ, Category.assoc]
        _ = M'.θ ≫ (M'.τ _).hom ≫ up := by rw [Category.assoc, ← hτ]
        _ = _ := (Category.assoc _ _ _).symm
    · simp only [Category.assoc, M'.θ_over, M'.τ_over, M'.σ_over]
  have hcomparison' := comparison_fixed_images M' hcard Ψ ψ hb hequiv'
  rcases hcomparison' with ⟨e', he', _, _, _⟩
  refine ⟨M', uq, up, hq, hp, e', hrootq, hrootp, he', ?_⟩
  let : Invertible (Fintype.card (ZMod p) : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  apply image_comparison_naturality
    (h)_*[ModuleCat L]
    (artinSchreierComparisonPIdempotent M Ψ)
    (artinSchreierComparisonQIdempotent M ψ)
    (artinSchreierComparisonPIdempotent M' Ψ)
    (artinSchreierComparisonQIdempotent M' ψ)
    (isotypicIdempotent_comp_self _ _ _ _ M.τ_add)
    _ _ _ _ e e' he he'
  · exact comparisonBaseMap_projector _ _ h up hp.w
      (fun d ↦ (M.τ d).hom) M.τ_over (fun d ↦ (M'.τ d).hom) M'.τ_over hτ Ψ
  · exact comparisonBaseMap_naturality _ _ _ _ h M.θ M.θ_over M'.θ M'.θ_over
      up hp.w uq hq.w hθ


/-- Finite-field characters have a unique nonzero trace parameter, and the character
summands of the degree-q and degree-p covers are naturally isomorphic lisse sheaves.
The isomorphism is oriented from the prime summand to the q summand so that its composite
with the image inclusion is exactly pullback of sections along the trace-polynomial map.
The last equation is its naturality square in adjoint form; the projector on the new prime
cover supplies the canonical retraction onto its image.

Source: Laumon (0.2), (1.1.3), (1.1.3.6), pp. 135 and 139–140, and the explicit
trace-polynomial comparison in the DAG proof
(blueprint: lem-a1-artin-schreier-prime-character-comparison).

Proof:
1. All character values lie in the p-th roots of unity. The nontrivial prime-field
   character identifies its additive group with those roots. Hence psi factors uniquely
   through an F_p-linear functional. Nondegeneracy of the trace pairing
   (lem-a1-trace-pairing-nondegenerate) identifies it with c ↦ Tr(bc), uniquely.
   Nontriviality excludes b=0. This is Laumon (0.2).
2. The trace-cover map (lem-a1-artin-schreier-trace-cover-map) supplies the covers,
   translations, and theta with theta sigma_c = tau_Tr(bc) theta. Both covers are finite
   etale torsors (also lem-fd-as-cover), and theta is surjective on geometric fibres.
3. The finite stalk formula (lemma-weil-pbc-finite-stalk-formula) identifies pushed-forward
   constant sheaves with functions on the finite geometric fibres. Pullback along theta
   is precomposition, hence injective, and intertwines the two translation actions.
4. Reindexing the character sum identifies each projector image with its eigensheaf.
   The trace identity makes theta pullback carry the prime eigensheaf to the q eigensheaf.
   Each geometric stalk is one dimensional by the regular representation of the torsor.
   The resulting injective map of lines is invertible; geometric stalks detect isomorphisms.
5. Finite etale local splitting (lem-weil-pbc-finite-etale-etale-local-split) trivializes
   the pushed-forward constant sheaves. On connected local pieces the translations are
   fixed permutations, so each projector image is a constant line, hence lisse.
6. Finite exchange (lemma-weil-pbc-finite-exchange), equivariant for translations,
   identifies the pulled-back universal sheaf of def-fd-artin-schreier-sheaf with the
   q-projector image. Exact pullback preserves images. The coordinate-preserving cartesian
   squares supplied by the trace-cover lemma identify the two new covers and theta with
   their base changes. On stalks, all arrows are precomposition on the same fibres.
   Thus the comparison commutes with pullback. The final equation writes this square
   after adjunction to h_* and the image inclusions; the prime projector retraction acts
   identically on the transported prime eigensheaf.
-/
theorem artinSchreier_prime_character_comparison (k : Type u) [Field k] [Fintype k]
    (p r ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hr : 1 ≤ r) (hcard : Fintype.card k = p ^ r) (hℓ : ℓ ≠ p)
    [Algebra (Padic ℓ) L] [IsAlgClosure (Padic ℓ) L]
    (Ψ : AddChar (ZMod p) L) (hΨ : Ψ ≠ 1) (ψ : AddChar k L) (hψ : ψ ≠ 1) :
    ∃ b : kˣ,
      (∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b : k) * c))) ∧
      (∀ b' : kˣ, (∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b' : k) * c))) →
        b' = b) ∧
      ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
        [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
        [QuasiCompact (X ↘ Spec (.of k))] (f : Γ(X, ⊤)),
      ∃ (M : ArtinSchreierTraceMaps k p r (b : k) X f)
        (e : image (artinSchreierComparisonPIdempotent M Ψ) ≅
          image (artinSchreierComparisonQIdempotent M ψ)),
        e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) =
          image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
            lowerStarConstantSheafMapOfOver
              (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
              (artinSchreierFunctionProjection X (p ^ r) f) M.θ M.θ_over ∧
        Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonQIdempotent M ψ)) ∧
        Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonPIdempotent M Ψ)) ∧
        Nonempty (artinSchreierComparisonSheafOf X ψ f ≅
          image (artinSchreierComparisonQIdempotent M ψ)) ∧
        ∀ (X' : Scheme.{u}) [X'.Over (Spec (.of k))]
          [IsSeparated (X' ↘ Spec (.of k))] [LocallyOfFiniteType (X' ↘ Spec (.of k))]
          [QuasiCompact (X' ↘ Spec (.of k))] (h : X' ⟶ X) [h.IsOver (Spec (.of k))],
        ∃ (M' : ArtinSchreierTraceMaps k p r (b : k) X' (h.appTop f))
          (uq : artinSchreierFunctionCover X' (p ^ r) (h.appTop f) ⟶
            artinSchreierFunctionCover X (p ^ r) f)
          (up : artinSchreierFunctionCover X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ⟶
            artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f))
          (hq : IsPullback uq (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f))
            (artinSchreierFunctionProjection X (p ^ r) f) h)
          (hp : IsPullback up (artinSchreierFunctionProjection X' p
              (artinSchreierBaseConstants k X' b * h.appTop f))
            (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)) h)
          (e' : image (artinSchreierComparisonPIdempotent M' Ψ) ≅
            image (artinSchreierComparisonQIdempotent M' ψ)),
          uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
            artinSchreierFunctionRoot X' (p ^ r) (h.appTop f) ∧
          up.appTop (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
            artinSchreierFunctionRoot X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ∧
          e'.hom ≫ image.ι (artinSchreierComparisonQIdempotent M' ψ) =
            image.ι (artinSchreierComparisonPIdempotent M' Ψ) ≫
              lowerStarConstantSheafMapOfOver
                (artinSchreierFunctionProjection X' p
                  (artinSchreierBaseConstants k X' b * h.appTop f))
                (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f)) M'.θ M'.θ_over ∧
          image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
              artinSchreierComparisonBaseMap
                (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
                (artinSchreierFunctionProjection X' p
                  (artinSchreierBaseConstants k X' b * h.appTop f)) h up hp.w ≫
              (h)_*[ModuleCat L].map
                (factorThruImage (artinSchreierComparisonPIdempotent M' Ψ)) ≫
              (h)_*[ModuleCat L].map e'.hom ≫
              (h)_*[ModuleCat L].map (image.ι (artinSchreierComparisonQIdempotent M' ψ)) =
            e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) ≫
              artinSchreierComparisonBaseMap
                (artinSchreierFunctionProjection X (p ^ r) f)
                (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f)) h uq hq.w := by
  have _ := hℓ
  obtain ⟨b, hb, hbu⟩ := exists_comparison_parameter k p Ψ hΨ ψ hψ
  refine ⟨b, hb, hbu, ?_⟩
  exact comparison_geometric k p r hr hcard Ψ ψ b hb


end

end AlgebraicGeometry.Etale
