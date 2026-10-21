/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Algebra.Homology.RingedSliceHomSourceShift
import Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons
import Sheaf.Algebra.Homology.RingedSliceEvaluationCoherence
import all Sheaf.Algebra.Homology.RingedSliceKoszulCoherence

/-! # Restriction of the normalized single coefficient dual

Source: Stacks Project, Tags 08JB, 08FI and 0A97.
(blueprint: lem-coef-signed-single-dual-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w w' a b x y
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses CategoryTheory.Pretriangulated.Opposite
namespace CategoryTheory

/-- Restriction of a single internal dual, including transport of the coefficient object.
Source: Stacks 08JB and 0A97.
(blueprint: lem-coef-signed-single-dual-restriction). -/
def closedDualRestrictionIso
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} {F : D ⥤ E}
    {O : D} {OU : E}
    (h : H ⋙ F ≅ (F.op.prod F) ⋙ HU) (o : F.obj O ≅ OU) :
    (Prod.sectL _ O ⋙ H) ⋙ F ≅ F.op ⋙ (Prod.sectL _ OU ⋙ HU) :=
  NatIso.ofComponents (fun X ↦ h.app (X, O) ≪≫
    HU.mapIso ((Iso.refl (F.op.obj X)).prod o)) (by
      intro X Y f
      have hn := h.hom.naturality (Prod.mkHom f (𝟙 O))
      dsimp only [Functor.comp_map, Functor.prod_map, Prod.sectL_map] at hn ⊢
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
      change F.map (H.map (Prod.mkHom f (𝟙 O))) ≫
          h.hom.app (Y, O) ≫ HU.map (Prod.mkHom (𝟙 _) o.hom) =
        (h.hom.app (X, O) ≫ HU.map (Prod.mkHom (𝟙 _) o.hom)) ≫
          HU.map (Prod.mkHom (F.op.map f) (𝟙 OU))
      rw [← Category.assoc, hn]
      simp only [Category.assoc, ← HU.map_comp]
      congr 2
      ext <;> simp)

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
private theorem symmetry_eq_of_model
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (σ : ∀ X Y : D.{c, v, r, w} J R,
      M.closed.tensor.obj (X, Y) ≅ M.closed.tensor.obj (Y, X))
    (hn : ∀ (X Y X' Y' : D.{c, v, r, w} J R) (f : X ⟶ X') (g : Y ⟶ Y'),
      M.closed.tensor.map (Prod.mkHom f g) ≫ (σ X' Y').hom =
        (σ X Y).hom ≫ M.closed.tensor.map (Prod.mkHom g f))
    (hm : ∀ (P Q : Complex.{c, v, r} J R)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
      ∃ β : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
        (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (V : Cᵒᵖ)
          (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
          (β.f k).val.app V
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y) =
            (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v}
              J R Q P q p k h' V y x) ∧
        (M.models.iso J R M.closed P Q hP hQ).hom ≫
          (σ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
          DerivedCategory.Q.map β ≫ (M.models.iso J R M.closed Q P hQ hP).hom) :
    ∀ X Y : D.{c, v, r, w} J R, (σ X Y).hom = (M.symmetric.braiding X Y).hom := by
  have base (P Q : Complex.{c, v, r} J R)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q) :
      (σ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        (M.symmetric.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom := by
    obtain ⟨β, hb, hβ⟩ := hm P Q hP hQ
    obtain ⟨γ, hg, hγ⟩ := M.symmetry_model P Q hP hQ
    have hbγ : β = γ := by
      apply tensorGenerator_ext.{c, v, r} J R P Q
      intro p q k hpq V x y
      exact (hb p q k hpq (by omega) V x y).trans
        (hg p q k hpq (by omega) V x y).symm
    subst γ
    exact (cancel_epi (M.models.iso J R M.closed P Q hP hQ).hom).mp (hβ.trans hγ.symm)
  intro X Y
  classical
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage X)
  obtain ⟨Q, g, hQ, _, hg, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage Y)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hg
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  let e' := asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso Y
  have hi : IsIso (Prod.mkHom e.hom e'.hom) :=
    (CategoryTheory.isIso_prod_iff (f := Prod.mkHom e.hom e'.hom)).mpr
      ⟨inferInstance, inferInstance⟩
  have : IsIso (M.closed.tensor.map (Prod.mkHom e.hom e'.hom)) := inferInstance
  apply (cancel_epi (M.closed.tensor.map (Prod.mkHom e.hom e'.hom))).mp
  rw [hn, base P Q hP hQ]
  let := M.closed.monoidal
  let := M.symmetric
  dsimp only [WeilConjectures.CoefficientClosedStructure.tensor]
  exact (BraidedCategory.braiding_naturality e.hom e'.hom).symm

end Site

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
  (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (R.over U))]

set_option quotPrecheck false
set_option hygiene false
local notation "H" => derivedInternalHomOfUniverses.{c, v, r, w} J R
local notation "HU" => derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)
local notation "O" => ringedSiteDualityUnit.{c, v, r, w} J R
local notation "OU" => ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U)
local notation "F" =>
  letI := SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  Functor.mapDerivedCategory.{w, w'}
  (C₁ := Modules.{c, v, r} J R)
  (C₂ := Modules.{max c v, v, r} (J.over U) (R.over U))
  (SheafOfModules.localizedSystemRestriction.{c, v, r} R U)
local notation "T" => Prod.sectL _ O ⋙ H
local notation "TU" => Prod.sectL _ OU ⋙ HU

set_option maxHeartbeats 600000 in
-- Normalize the dependent endpoints of the two derived restriction presentations.
/-- The canonical slice comparisons preserve evaluation and the normalized signed single dual.
Source: Stacks Project, Tags 08JB, 08FI and 0A97.
(blueprint: lem-coef-signed-single-dual-restriction).

Proof: use termwise exact restriction, with its fixed derived localization comparison.
Restriction preserves K-injectivity by the exact extension-by-zero adjunction. On a
K-injective target the Hom comparison is the identity on local families of maps on
successive slices; its differential is unchanged. Restrict the coefficient unit in degree
zero. On K-flat sources the tensor comparison is identity on pure tensor generators.
These comparisons preserve evaluation and Koszul interchange. For the single
source shift, reindex the local Hom projections and multiply the degree-q projection by
(-1)^(m*q). Restriction keeps each sign and reindexing unchanged, so it preserves the
normalized source shifts at m=1 and m=-1. The leading minus for the opposite shift 1 is
preserved as well. Naturality in the target transports this calculation through the
coefficient-unit isomorphism. In Lean, the normalized comparisons, evaluation coherence,
and Koszul coherence are the existing slice theorems. The source-shift calculation is
ringedSlice_hom_sourceShift. Pure-tensor extensionality identifies the normalized
symmetry families with M.symmetric and MU.symmetric. No bidual or triangle assertion
is included in this statement. -/
theorem ringedSiteSignedDual_restriction
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U))
    : ∃ (h : H ⋙ F ≅ ((F).op.prod F) ⋙ HU) (o : (F).obj O ≅ OU)
      (t : M.closed.tensor ⋙ F ≅ ((F).prod F) ⋙ MU.closed.tensor),
      (∀ X Y : D.{c, v, r, w} J R,
        (F).map (M.closed.evaluation X Y) =
          t.hom.app ((H).obj (op X, Y), X) ≫
            MU.closed.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 _)) ≫
              MU.closed.evaluation ((F).obj X) ((F).obj Y)) ∧
      (∀ X Y : D.{c, v, r, w} J R,
        (F).map (M.symmetric.braiding X Y).hom ≫ t.hom.app (Y, X) =
          t.hom.app (X, Y) ≫ (MU.symmetric.braiding ((F).obj X) ((F).obj Y)).hom) ∧
      (∀ (X : D.{c, v, r, w} J R) (n : ℤ),
        (F).map ((sourceShift.{c, v, r, w} J R X n).hom.app O) ≫
            (closedDualRestrictionIso h o).hom.app (op (X⟦n⟧)) =
          ((F).commShiftIso (-n)).hom.app ((T).obj (op X)) ≫
            ((closedDualRestrictionIso h o).hom.app (op X))⟦-n⟧' ≫
            (sourceShift.{max c v, v, r, w'} (J.over U) (R.over U) ((F).obj X) n).hom.app OU ≫
            (HU).map (Prod.mkHom (((F).commShiftIso n).hom.app X).op (𝟙 OU))) := by
  classical
  obtain ⟨d, hd⟩ := (ringedSlice_normalizedComparisons.{c, v, r, w, w'} J R U
    M.closed M.models MU.closed MU.models).some
  let h : H ⋙ F ≅ ((F).op.prod F) ⋙ HU :=
    NatIso.ofComponents (fun X ↦ d.eta X.1.unop X.2) (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      simpa only [Functor.comp_map, Functor.prod_map, Functor.op_map, Quiver.Hom.op_unop,
        ringedSliceDerivedRestriction, ringedDerivedRestrictionGeneral,
        SheafOfModules.localizedSystemRestriction, Prod.mkHom] using
        d.eta_naturality X₁.unop X₂ Y₁.unop Y₂ f₁.unop f₂)
  let t : M.closed.tensor ⋙ F ≅ ((F).prod F) ⋙ MU.closed.tensor :=
    NatIso.ofComponents (fun X ↦ d.rho X.1 X.2) (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      simpa only [Functor.comp_map, Functor.prod_map, ringedSliceDerivedRestriction,
        ringedDerivedRestrictionGeneral, SheafOfModules.localizedSystemRestriction,
        Prod.mkHom] using d.rho_naturality X₁ X₂ Y₁ Y₂ f₁ f₂)
  let : HasDerivedCategory.{w'} (SheafOfModules.{max c v r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w'}
      (Modules.{max c v, v, r} (J.over U) (R.over U)))
  let o : (F).obj O ≅ OU := ringedDerivedRingRestrictionIsoGeneral
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U
  have he (X Y : D.{c, v, r, w} J R) :
      (F).map (M.closed.evaluation X Y) =
        t.hom.app ((H).obj (op X, Y), X) ≫
          MU.closed.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 _)) ≫
            MU.closed.evaluation ((F).obj X) ((F).obj Y) := by
    have hh := ringedSlice_evaluation_coherence.{c, v, r, w, w'} J R U
      M.closed M.models MU.closed MU.models d hd.1 hd.2.1 X Y
    apply (cancel_epi (d.rho ((H).obj (op X, Y)) X).inv).mp
    dsimp only [h, t, NatIso.ofComponents_hom_app]
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ringedSliceDerivedRestriction, ringedDerivedRestrictionGeneral,
      SheafOfModules.localizedSystemRestriction, Prod.mkHom] using hh
  have hσ : ∀ X Y, (d.sigma X Y).hom = (M.symmetric.braiding X Y).hom := by
    apply symmetry_eq_of_model.{c, v, r, w} J R M d.sigma d.sigma_naturality
    intro P Q hP hQ
    obtain ⟨β, hb, he⟩ := hd.2.2.1 P Q hP hQ
    exact ⟨β.hom, hb, he⟩
  have hσU : ∀ X Y, (d.sigmaU X Y).hom = (MU.symmetric.braiding X Y).hom := by
    apply symmetry_eq_of_model.{max c v, v, r, w'} (J.over U) (R.over U)
      MU d.sigmaU d.sigmaU_naturality
    intro P Q hP hQ
    obtain ⟨β, hb, he⟩ := hd.2.2.2 P Q hP hQ
    exact ⟨β.hom, hb, he⟩
  refine ⟨h, o, t, he, ?_, ?_⟩
  · intro X Y
    have hh := ringedSlice_koszul_coherence.{c, v, r, w, w'} J R U
      M.closed M.models MU.closed MU.models d hd X Y
    simpa only [hσ, hσU, t, NatIso.ofComponents_hom_app,
      ringedSliceDerivedRestriction, ringedDerivedRestrictionGeneral,
      SheafOfModules.localizedSystemRestriction] using hh
  · intro X n
    have hh := ringedSlice_hom_sourceShift.{c, v, r, w, w'} J R U M MU d hd.2.1 X O n
    dsimp only [closedDualRestrictionIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
    simp only [Functor.map_comp, Category.assoc]
    change (F).map ((sourceShift J R X n).hom.app O) ≫
        (d.eta (X⟦n⟧) O).hom ≫
        (HU).map (Prod.mkHom (𝟙 (op ((F).obj (X⟦n⟧)))) o.hom) =
      ((F).commShiftIso (-n)).hom.app ((H).obj (op X, O)) ≫
        (d.eta X O).hom⟦-n⟧' ≫
        ((HU).map (Prod.mkHom (𝟙 (op ((F).obj X))) o.hom))⟦-n⟧' ≫
        (sourceShift (J.over U) (R.over U) ((F).obj X) n).hom.app OU ≫
        (HU).map (Prod.mkHom (((F).commShiftIso n).hom.app X).op (𝟙 OU))
    rw [← Category.assoc, hh]
    simp only [Category.assoc]
    have hn := (sourceShift.{max c v, v, r, w'} (J.over U) (R.over U)
      ((F).obj X) n).hom.naturality o.hom
    change ((HU).map (Prod.mkHom (𝟙 (op ((F).obj X))) o.hom))⟦-n⟧' ≫
        (sourceShift (J.over U) (R.over U) ((F).obj X) n).hom.app OU =
      (sourceShift (J.over U) (R.over U) ((F).obj X) n).hom.app ((F).obj O) ≫
        (HU).map (Prod.mkHom (𝟙 (op (((F).obj X)⟦n⟧))) o.hom) at hn
    rw [reassoc_of% hn]
    simp only [← (HU).map_comp]
    congr 4
    ext <;> simp

end Site
end CategoryTheory
