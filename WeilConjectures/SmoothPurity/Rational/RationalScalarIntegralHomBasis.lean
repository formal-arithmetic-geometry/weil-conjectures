/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralScalarCoordinates
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientIntegralTrace
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # The integral finite free Hom formula for completed scalar extension

For a finite extension `L/E` of finite extensions of `ℚ_ℓ` and an `𝒪_E`-basis `b` of `𝒪_L`,
every morphism `Ext X ⟶ Ext Z` of the completed scalar extensions of derived complete
complexes is uniquely of the form `∑ i, b i • Ext (h i)`.

Proof: extension ⊣ restriction on derived categories identifies `Hom(Ord X, Ord Z)` with
`Hom(X, Res Ord Z)`, and the coordinates of `integralOrdinaryScalar_coordinates` exhibit
`Res Ord Z` as `⊕ᵢ Z`. On complete objects the exact ordinary extension is the completed one.
(blueprint: def-weil-rationalization-karoubi).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Postcomposition with an isomorphism is bijective. -/
private lemma bijective_comp_hom {C : Type*} [Category C] {X A B : C} (f : A ≅ B) :
    Function.Bijective fun g : X ⟶ A ↦ g ≫ f.hom :=
  (⟨fun g ↦ g ≫ f.hom, fun g ↦ g ≫ f.inv, fun g ↦ by simp, fun g ↦ by simp⟩ :
    (X ⟶ A) ≃ (X ⟶ B)).bijective

/-- Componentwise postcomposition with an isomorphism is bijective. -/
private lemma bijective_pi_comp_hom (d : ℕ) {C : Type*} [Category C] {X A B : C} (f : A ≅ B) :
    Function.Bijective fun (h : Fin d → (X ⟶ A)) (i : Fin d) ↦ h i ≫ f.hom :=
  (Equiv.piCongrRight fun _ : Fin d ↦ (⟨fun g ↦ g ≫ f.hom, fun g ↦ g ≫ f.inv,
    fun g ↦ by simp, fun g ↦ by simp⟩ : (X ⟶ A) ≃ (X ⟶ B))).bijective

/-- The derived scalar action on the image of a complex is the termwise multiplication by the
constant section. -/
theorem smul_id_Q_obj (x : Padic.coefficientExtensionIntegers l L)
    (K : CochainComplex (integralTowerModules l L Y) ℤ) :
    x • 𝟙 (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((integralScalarChainAction l L Y x).app K) := by
  have h := (sfIntegralConstructible_linear l L Y).1 x (DerivedCategory.Q.obj K) _ (𝟙 _)
  refine h.trans ?_
  erw [Category.comp_id, integralScalarDerivedAction_app_Q]

/-- The constant-section chain action is termwise multiplication. -/
theorem integralScalarChainAction_app_f (x : Padic.coefficientExtensionIntegers l L)
    (K : CochainComplex (integralTowerModules l L Y) ℤ) (n : ℤ) :
    ((integralScalarChainAction l L Y x).app K).f n = (integralScalarSMul l L Y x).app (K.X n) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact (integralScalarChainAction_existsUnique l L Y x).exists.choose_spec K n U y

set_option profiler true in
set_option maxHeartbeats 1000000 in
-- The transports between `Q ⋙ F.mapDerivedCategory` and `F.mapHomologicalComplex ⋙ Q` are slow.
/-- The finite free Hom formula for the exact ordinary scalar extension on derived categories:
for an `𝒪_E`-basis `b` of `𝒪_L`, every morphism `Ord X ⟶ Ord Z` is uniquely
`∑ i, b i • Ord (h i)`.
Source: Bhatt--Scholze, Lemma 6.8.2(1) and Proposition 6.8.14(2). -/
theorem integralOrdinaryDerivedScalar_map_basis_bijective :
    ∃ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L),
      (letI := (integralScalarIntegerInclusion l E L ι).toAlgebra
        ∃ b' : Module.Basis (Fin d) (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l L), ⇑b' = b) ∧
      ∀ X Z : DerivedCategory (integralTowerModules l E Y),
        Function.Bijective fun h : Fin d → (X ⟶ Z) ↦
          ∑ i, b i • (integralOrdinaryDerivedScalar l E L ι Y).map (h i) := by
  obtain ⟨d, b, a, π, hb, hA, hB⟩ := integralOrdinaryScalar_coordinates l E L ι Y
  refine ⟨d, b, hb, fun X Z ↦ ?_⟩
  let Res := SheafOfModules.restrictScalars ((sheafCompose
    (AlgebraicGeometry.Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralCompletedScalarMap l E L ι Y))
  let Ord := integralOrdinaryScalar l E L ι Y
  have hRes : rationalScalarModuleRestriction l E L ι Y = SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι Y)) := by
    rw [← completedCoefficientMap_eq_integralCompletedScalarMap l E Y L ι]
    rfl
  have hlim := (rationalScalarModuleRestriction_exact l E L ι Y).1
  have hcolim := (rationalScalarModuleRestriction_exact l E L ι Y).2
  rw [hRes] at hlim hcolim
  let fR := Res.mapDerivedCategoryFactors
  let fO := Ord.mapDerivedCategoryFactors
  let : CatCommSq (Res.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q Res.mapDerivedCategory := ⟨fR.symm⟩
  let : CatCommSq (Ord.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q Ord.mapDerivedCategory := ⟨fO.symm⟩
  let da : Ord.mapDerivedCategory ⊣ Res.mapDerivedCategory :=
    (a.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) Ord.mapDerivedCategory Res.mapDerivedCategory
  let ιZ (i : Fin d) (Z : DerivedCategory (integralTowerModules l E Y)) :
      Z ⟶ Res.mapDerivedCategory.obj (Ord.mapDerivedCategory.obj Z) :=
    da.unit.app Z ≫ Res.mapDerivedCategory.map (b i • 𝟙 _)
  let Θ (Z : DerivedCategory (integralTowerModules l E Y)) (h : Fin d → (X ⟶ Z)) :
      X ⟶ Res.mapDerivedCategory.obj (Ord.mapDerivedCategory.obj Z) := ∑ i, h i ≫ ιZ i Z
  have hΘ (h : Fin d → (X ⟶ Z)) : da.homEquiv X _
      (∑ i, b i • (integralOrdinaryDerivedScalar l E L ι Y).map (h i)) = Θ Z h := by
    rw [Adjunction.homEquiv_unit, Functor.map_sum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Category.comp_id ((integralOrdinaryDerivedScalar l E L ι Y).map (h i)),
      ← Linear.comp_smul, Functor.map_comp, ← Category.assoc]
    erw [da.unit_naturality]
    rw [Category.assoc]
  have hnat (i : Fin d) {Z Z' : DerivedCategory (integralTowerModules l E Y)} (f : Z ⟶ Z') :
      f ≫ ιZ i Z' = ιZ i Z ≫ Res.mapDerivedCategory.map (Ord.mapDerivedCategory.map f) := by
    simp only [ιZ]
    rw [← Category.assoc, ← da.unit_naturality, Category.assoc, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]
  have hQ (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      Function.Bijective (Θ (DerivedCategory.Q.obj P)) := by
    let OP := (Ord.mapHomologicalComplex (.up ℤ)).obj P
    let unitP := (a.mapHomologicalComplex (.up ℤ)).unit.app P
    let smulC (i : Fin d) : OP ⟶ OP := (integralScalarChainAction l L Y (b i)).app OP
    let πC (j : Fin d) : (Res.mapHomologicalComplex (.up ℤ)).obj OP ⟶ P :=
(NatTrans.mapHomologicalComplex (π j) (.up ℤ)).app P
    have hιQ (i : Fin d) : ιZ i (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (unitP ≫ (Res.mapHomologicalComplex (.up ℤ)).map (smulC i)) ≫
          fR.inv.app OP ≫ Res.mapDerivedCategory.map (fO.inv.app P) := by
      have hs : b i • 𝟙 (Ord.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
          fO.hom.app P ≫ (b i • 𝟙 (DerivedCategory.Q.obj OP)) ≫ fO.inv.app P := by
        erw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id_app]
        rfl
      have hr : Res.mapDerivedCategory.map (DerivedCategory.Q.map (smulC i)) =
          fR.hom.app OP ≫ DerivedCategory.Q.map ((Res.mapHomologicalComplex (.up ℤ)).map
            (smulC i)) ≫ fR.inv.app OP := by
        have h := fR.hom.naturality (smulC i)
        simp only [Functor.comp_map] at h
        rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      simp only [ιZ, hs]
      erw [smul_id_Q_obj, Adjunction.localization_unit_app]
      have hcR : (CatCommSq.iso (Res.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
          DerivedCategory.Q Res.mapDerivedCategory).hom = fR.inv := rfl
      have hcO : (CatCommSq.iso (Ord.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
          DerivedCategory.Q Ord.mapDerivedCategory).hom = fO.inv := rfl
      rw [hcR, hcO]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, hr]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app_assoc]
    let πP (j : Fin d) : Res.mapDerivedCategory.obj (Ord.mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) ⟶ DerivedCategory.Q.obj P :=
      Res.mapDerivedCategory.map (fO.hom.app P) ≫ fR.hom.app OP ≫ DerivedCategory.Q.map (πC j)
    have hAc (i j : Fin d) : unitP ≫ (Res.mapHomologicalComplex (.up ℤ)).map (smulC i) ≫ πC j =
        if i = j then 𝟙 P else 0 := by
      ext n : 1
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
        smulC, πC, unitP, integralScalarChainAction_app_f]
      refine (hA i j (P.X n)).trans ?_
      split_ifs <;> simp
    have hBc : ∑ j, πC j ≫ unitP ≫ (Res.mapHomologicalComplex (.up ℤ)).map (smulC j) = 𝟙 _ := by
      ext n : 1
      refine (map_sum (HomologicalComplex.Hom.fAddMonoidHom
        (C₁ := (Res.mapHomologicalComplex (.up ℤ)).obj OP)
        (C₂ := (Res.mapHomologicalComplex (.up ℤ)).obj OP) n) _ Finset.univ).trans ?_
      change ∑ j, (πC j ≫ unitP ≫ (Res.mapHomologicalComplex (.up ℤ)).map (smulC j)).f n = _
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
        smulC, πC, unitP, integralScalarChainAction_app_f]
      exact hB (P.X n)
    have hAP (i j : Fin d) : ιZ i (DerivedCategory.Q.obj P) ≫ πP j = if i = j then 𝟙 _ else 0 := by
      rw [hιQ]
      simp only [πP, Category.assoc]
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
      rw [← Functor.map_comp, Category.assoc, hAc]
      split_ifs <;> simp
    have hBP : ∑ j, πP j ≫ ιZ j (DerivedCategory.Q.obj P) = 𝟙 _ := by
      have hj (j : Fin d) : πP j ≫ ιZ j (DerivedCategory.Q.obj P) =
          Res.mapDerivedCategory.map (fO.hom.app P) ≫ fR.hom.app OP ≫ DerivedCategory.Q.map
            (πC j ≫ unitP ≫ (Res.mapHomologicalComplex (.up ℤ)).map (smulC j)) ≫
              fR.inv.app OP ≫ Res.mapDerivedCategory.map (fO.inv.app P) := by
        rw [hιQ]
        simp only [πP, Category.assoc, Functor.map_comp]
      rw [Finset.sum_congr rfl fun j _ ↦ hj j]
      simp only [← Preadditive.comp_sum, ← Preadditive.sum_comp, ← Functor.map_sum, hBc]
      rw [CategoryTheory.Functor.map_id]
      erw [Category.id_comp, Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      rfl
    refine ⟨fun h h' hh ↦ funext fun j ↦ ?_, fun g ↦ ⟨fun j ↦ g ≫ πP j, ?_⟩⟩
    · have hj (h : Fin d → (X ⟶ DerivedCategory.Q.obj P)) : Θ _ h ≫ πP j = h j := by
        simp only [Θ, Preadditive.sum_comp, Category.assoc, hAP]
        rw [Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)]
        simp
      rw [← hj h, ← hj h', hh]
    · simp only [Θ, Category.assoc, ← Preadditive.comp_sum, hBP, Category.comp_id]
  have hbij : Function.Bijective (Θ Z) := by
    let P := DerivedCategory.Q.objPreimage Z
    let e : DerivedCategory.Q.obj P ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
    have hc : Θ Z = (fun g ↦ g ≫ Res.mapDerivedCategory.map (Ord.mapDerivedCategory.map e.hom)) ∘
        Θ (DerivedCategory.Q.obj P) ∘ fun h i ↦ h i ≫ e.inv := by
      funext h
      simp only [Function.comp_apply, Θ, Preadditive.sum_comp, Category.assoc]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hnat, Iso.inv_hom_id_assoc]
    rw [hc]
    exact (bijective_comp_hom (Res.mapDerivedCategory.mapIso
      (Ord.mapDerivedCategory.mapIso e))).comp ((hQ P).comp (bijective_pi_comp_hom d e.symm))
  have hc : (fun h : Fin d → (X ⟶ Z) ↦
      ∑ i, b i • (integralOrdinaryDerivedScalar l E L ι Y).map (h i)) =
      (da.homEquiv X _).symm ∘ Θ Z := by
    funext h
    exact ((da.homEquiv X _).symm_apply_eq.2 (hΘ h).symm).symm
  rw [hc]
  exact (da.homEquiv X _).symm.bijective.comp hbij

/-- The finite free Hom formula for the completed integral scalar extension of integral
constructible complexes: for an `𝒪_E`-basis `β` of `𝒪_L`, every morphism `Ext N ⟶ Ext Z` is
uniquely `∑ i, β i • Ext (h i)`.
Source: Bhatt--Scholze, Lemma 6.8.2(1), Propositions 3.5.1 and 6.8.14(2).
Proof: on complete objects the completed scalar extension is the exact ordinary one
(`isIso_completedScalarComparison_app`), and the comparison is natural and linear, so this is
`integralOrdinaryDerivedScalar_map_basis_bijective`. -/
theorem sfConstructibleIntegralScalarExtension_map_basis_bijective (p : ℕ) (hl : l ≠ p) :
    letI := (integralScalarIntegerInclusion l E L ι).toAlgebra
    ∃ (d : ℕ) (β : Module.Basis (Fin d) (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l L)),
      ∀ N Z : sfIntegralConstructibleCategory l E Y,
        Function.Bijective fun h : Fin d → (N ⟶ Z) ↦
          ∑ i, β i • (sfConstructibleIntegralScalarExtension p l hl E L ι Y).map (h i) := by
  obtain ⟨d, b, ⟨β, hβ⟩, hO⟩ := integralOrdinaryDerivedScalar_map_basis_bijective l E L ι Y
  refine ⟨d, β, fun N Z ↦ ?_⟩
  let c := (integralOrdinaryDerivedScalarIso l E Y L ι).hom ≫ completedScalarComparison l E L ι Y
  have hN : IsIso (c.app N.obj) := IsIso.comp_isIso' inferInstance
    (isIso_completedScalarComparison_app l E Y L ι N.obj N.property.1)
  have hZ : IsIso (c.app Z.obj) := IsIso.comp_isIso' inferInstance
    (isIso_completedScalarComparison_app l E Y L ι Z.obj Z.property.1)
  let eE := (sfIntegralConstructible l E Y).fullyFaithfulι.homEquiv (X := N) (Y := Z)
  let F := sfConstructibleIntegralScalarExtension p l hl E L ι Y
  let eL := (sfIntegralConstructible l L Y).fullyFaithfulι.homEquiv (X := F.obj N) (Y := F.obj Z)
  have hc : (fun h : Fin d → (N ⟶ Z) ↦ ∑ i, β i • F.map (h i)) =
      eL.symm ∘ (Iso.homCongr (asIso (c.app N.obj)) (asIso (c.app Z.obj))) ∘
        (fun h : Fin d → (N.obj ⟶ Z.obj) ↦
          ∑ i, b i • (integralOrdinaryDerivedScalar l E L ι Y).map (h i)) ∘
          fun h i ↦ eE (h i) := by
    funext h
    apply eL.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Iso.homCongr_apply, asIso_inv,
      asIso_hom, Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp]
    rw [Functor.FullyFaithful.homEquiv_apply, Functor.map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Functor.map_smul, hβ]
    congr 1
    exact (IsIso.eq_inv_comp (c.app N.obj)).mpr (c.naturality (eE (h i))).symm
  rw [hc]
  exact eL.symm.bijective.comp ((Iso.homCongr _ _).bijective.comp
    (hO N.obj Z.obj |>.comp (Equiv.piCongrRight fun _ ↦ eE).bijective))

end WeilConjectures
