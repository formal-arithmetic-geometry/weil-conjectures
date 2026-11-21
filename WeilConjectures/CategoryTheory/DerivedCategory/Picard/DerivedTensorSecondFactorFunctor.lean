/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.Picard.MixedTensorPointwiseLeftDerived
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Derived tensor with a fixed complex in the second factor

Source: Stacks Project, More on Algebra, Tags 064L and 06Y6 and Section 06Y5.

The tensor bifunctor is the mixed module tensor, totalized in the order `(E, N)`.
Thus the differential is `d_E ⊗ 1 + (-1)^p 1 ⊗ d_N`, and the `A`-action comes from `N`.
K-flatness uses the ordinary-module specialization of the ringed-site notion.
-/

@[expose] public section

universe u wR wA

open CategoryTheory

namespace DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

set_option quotPrecheck false in
local notation "QR" => (Q : CochainComplex (ModuleCat R) ℤ ⥤
  DerivedCategory (ModuleCat R))
set_option quotPrecheck false in
local notation "QA" => (Q : CochainComplex (ModuleCat A) ℤ ⥤
  DerivedCategory (ModuleCat A))
set_option quotPrecheck false in
local notation "W" => HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)

/-- The derived tensor product with a fixed second factor `N` exists as a functor in `N`, and is
a triangulated left derived functor with the compatibilities stated below.
Source: Stacks Project, Tags 064L and 06Y6, construction in Section 06Y5. -/
theorem exists_derivedTensor_second_factor_functor (f : R →+* A) :
    let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
    (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ)
      (E E' : CochainComplex (ModuleCat.{u} R) ℤ) (a : E ⟶ E'),
      QuasiIso a → (W).kFlat E → (W).kFlat E' → QuasiIso ((B.map a).app N)) ∧
    ∃ T : CochainComplex (ModuleCat.{u} A) ℤ ⥤
        (DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A)),
      ∃ ε : ∀ N : CochainComplex (ModuleCat.{u} A) ℤ,
          QR ⋙ T.obj N ⟶ B.flip.obj N ⋙ QA,
        (∀ N, (T.obj N).IsLeftDerivedFunctor (ε N) W) ∧
        (∀ N, ∃ c : (T.obj N).CommShift ℤ,
          letI := c
          (T.obj N).IsTriangulated) ∧
        (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ)
          (F : CochainComplex (ModuleCat.{u} R) ℤ),
          (W).kFlat F → IsIso ((ε N).app F)) ∧
        (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ)
          (E F : CochainComplex (ModuleCat.{u} R) ℤ) (s : F ⟶ E),
          QuasiIso s → (W).kFlat F →
          ∃! e : (T.obj N).obj ((QR).obj E) ≅ (QA).obj ((B.obj F).obj N),
            (T.obj N).map ((QR).map s) ≫ e.hom = (ε N).app F) ∧
        (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ)
          (E F₁ F₂ F₃ : CochainComplex (ModuleCat.{u} R) ℤ)
          (e₁ : (T.obj N).obj ((QR).obj E) ≅ (QA).obj ((B.obj F₁).obj N))
          (e₂ : (T.obj N).obj ((QR).obj E) ≅ (QA).obj ((B.obj F₂).obj N))
          (e₃ : (T.obj N).obj ((QR).obj E) ≅ (QA).obj ((B.obj F₃).obj N)),
          (e₁.symm ≪≫ e₂) ≪≫ (e₂.symm ≪≫ e₃) = e₁.symm ≪≫ e₃) ∧
        (∀ (N N' : CochainComplex (ModuleCat.{u} A) ℤ) (u : N ⟶ N')
          (F : CochainComplex (ModuleCat.{u} R) ℤ),
          (T.map u).app ((QR).obj F) ≫ (ε N').app F =
            (ε N).app F ≫ (QA).map ((B.obj F).map u)) ∧
        (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ), T.map (𝟙 N) = 𝟙 (T.obj N)) ∧
        (∀ (N N' N'' : CochainComplex (ModuleCat.{u} A) ℤ) (u : N ⟶ N') (v : N' ⟶ N''),
          T.map (u ≫ v) = T.map u ≫ T.map v) ∧
        (∀ (N N' : CochainComplex (ModuleCat.{u} A) ℤ) (u : N ⟶ N'),
          QuasiIso u →
          (∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
            (W).kFlat F → QuasiIso ((B.obj F).map u)) ∧ IsIso (T.map u)) := by
  classical
  dsimp only
  let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
  obtain ⟨hfirst, hsecond⟩ := CochainComplex.mixedTensor_kFlat_quasiIso f
  have hex := exists_mixedTensor_pointwise_leftDerived.{u, wR, wA} f
  choose L ε hderived htri hcompute using hex
  let (N : CochainComplex (ModuleCat.{u} A) ℤ) := hderived N
  let H := B.flip ⋙ (Functor.whiskeringRight _ _ _).obj QA
  let T : CochainComplex (ModuleCat.{u} A) ℤ ⥤
      (DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A)) :=
    { obj := L
      map := fun {N N'} u ↦
        Functor.leftDerivedNatTrans (L N) (L N') (ε N) (ε N') W (H.map u)
      map_id := fun N ↦ by
        rw [H.map_id]
        exact Functor.leftDerivedNatTrans_id (L N) (ε N) W
      map_comp := fun u v ↦ by
        rw [H.map_comp]
        exact (Functor.leftDerivedNatTrans_comp _ _ _ _ _ _ W _ _).symm }
  have hnat (N N' : CochainComplex (ModuleCat.{u} A) ℤ) (u : N ⟶ N')
      (F : CochainComplex (ModuleCat.{u} R) ℤ) :
      (T.map u).app ((QR).obj F) ≫ (ε N').app F =
        (ε N).app F ≫ (QA).map ((B.obj F).map u) := by
    exact Functor.leftDerivedNatTrans_app (L N) (L N') (ε N) (ε N') W (H.map u) F
  refine ⟨hfirst, T, ε, hderived, htri, hcompute, ?_, ?_, hnat,
    T.map_id, (fun _ _ _ u v ↦ T.map_comp u v), ?_⟩
  · intro N E F s hs hF
    let := hs
    let := hcompute N F hF
    have : IsIso ((QR).map s) := by
      exact (isIso_Q_map_iff_quasiIso (ModuleCat R) s).2 hs
    refine ⟨(asIso ((T.obj N).map ((QR).map s))).symm ≪≫ asIso ((ε N).app F),
      ?_, ?_⟩
    · simp
    · intro e he
      apply Iso.ext
      apply (cancel_epi ((T.obj N).map ((QR).map s))).1
      simpa using he
  · intro N E F₁ F₂ F₃ e₁ e₂ e₃
    ext
    simp
  · intro N N' u hu
    refine ⟨hsecond N N' u hu, ?_⟩
    apply (NatTrans.isIso_iff_isIso_app (T.map u)).2
    intro X
    have : (QR).EssSurj := Localization.essSurj QR W
    let E := (QR).objPreimage X
    let Λ := (Classical.choice (inferInstance :
      Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
    let F := Λ.resolutionFunctor.obj E
    let s := Λ.resolutionNatTrans.app E
    have hs : QuasiIso s := inferInstance
    have hF : (W).kFlat F :=
      Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le E
    have : IsIso ((QR).map s) := (isIso_Q_map_iff_quasiIso (ModuleCat R) s).2 hs
    let e : (QR).obj F ≅ X := asIso ((QR).map s) ≪≫ (QR).objObjPreimageIso X
    rw [← NatTrans.isIso_app_iff_of_iso (T.map u) e]
    have := hcompute N F hF
    have := hcompute N' F hF
    have hq := hsecond N N' u hu F hF
    have : IsIso ((QA).map ((B.obj F).map u)) :=
      (isIso_Q_map_iff_quasiIso (ModuleCat A) _).2 hq
    have : IsIso ((T.map u).app ((QR).obj F) ≫ (ε N').app F) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((ε N').app F)

end DerivedCategory
