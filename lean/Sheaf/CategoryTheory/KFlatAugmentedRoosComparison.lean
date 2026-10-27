/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.KFlatAugmentedRoosDefinitions
import Sheaf.CategoryTheory.KFlatRoosTensorDescent
import Sheaf.CategoryTheory.KFlatRoosDerivedComparison
import Sheaf.CategoryTheory.KFlatRoosSignedMap
import Sheaf.CategoryTheory.KFlatRoosProductCriterion
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # K-flat tensor comparison with augmented derived Roos limits

The universal derived comparison is normalized by the explicit signed fibre map.
The comparison interface is re-exported unchanged from the definitions module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] SheafOfModules.monoidalCategory
  CategoryTheory.KFlatAugmentedRoos.signedFiberMap
  CategoryTheory.KFlatAugmentedRoos.tensorCoconeIso
  CategoryTheory.KFlatAugmentedRoos.SignedCoordinates
  CategoryTheory.KFlatAugmentedRoos.productComparisonMap
  CategoryTheory.KFlatAugmentedRoos.limitComparisonMap
universe u v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex


namespace CategoryTheory.KFlatAugmentedRoos

private lemma comparison_tower_grothendieck
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{r} A] :
    IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

end CategoryTheory.KFlatAugmentedRoos

namespace CategoryTheory

/-- Tensor by every K-flat complex has a canonical natural comparison with total derived
inverse limit, represented on every injective tower resolution by the signed Roos map.
If its canonical derived product comparison is invertible, so is this comparison.
It preserves the entire canonical augmented map, including the zero shifted coordinate.

Source: Stacks Project, sites-cohomology.tex, Tags 0941, 06YM, 06YP, 06YS and 06YT;
derived.tex Tags 070I, 0BK6 and 014A; blueprint det-lem-int-tensor-product, first paragraph
(blueprint: lem-sfb-kflat-augmented-roos-comparison).

Proof: localize the signed total tensor in both tower and coefficient categories.
K-flat resolutions of the other factor prove invariance under quasi-isomorphisms
between K-flat tensor arguments. The limit functor factors through homotopy; the
K-injective derivability structure makes its right derivation absolute. Apply its
universal property to the ordinary limit comparison to construct beta. Its unit
identity gives the formula on arbitrary K-injective resolutions, naturality in the
tensor argument, and the entire augmentation equation. The explicit tensor/cone
and tensor/shift comparisons construct psi and give its two signed summand formulas.
The limit-inclusion square identifies this representative with beta. On injective
towers the products are derived products and the limit inclusions are
quasi-isomorphisms. The product hypothesis makes Qb invertible by its projections;
the mapping-cone triangle then makes Qpsi and Qtheta invertible, hence beta too. -/
theorem kFlatAugmentedRoosComparison
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.TotalTensorSigns.Modules R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.TotalTensorSigns.Modules R)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.TotalTensorSigns.Modules R) ⥤
      DerivedCategory.{w} (SheafOfModules.TotalTensorSigns.Modules R))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SheafOfModules.TotalTensorSigns.Modules R)
        (.up ℤ))) :
    KFlatAugmentedRoos.ComparisonFormulas
      (SheafOfModules.TotalTensorSigns.total R)
      CochainComplex.IsKFlatIndependentCoefficients
      (fun A ↦ KFlatAugmentedRoos.SignedCoordinates A)
      RF η := by
  classical
  let := _hRF
  let := SheafOfModules.isGrothendieckAbelian_coefficientUniverse
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let := KFlatAugmentedRoos.comparison_tower_grothendieck
    (SheafOfModules.TotalTensorSigns.Modules R)
  let : HasCountableProducts
      (DerivedCategory.{w} (SheafOfModules.TotalTensorSigns.Modules R)) := inferInstance
  open KFlatAugmentedRoos SheafOfModules.TotalTensorSigns in
    let T := localizedTensor R
    let e := localizedTensorIso R
    let S := localizedTowerTensor R
    let eS := localizedTowerTensorIso R
    let hAbs (K : {A : CochainComplex (Modules R) ℤ //
        IsKFlatIndependentCoefficients A}) := comparison_absolute (T K) RF η
    let β (K : {A : CochainComplex (Modules R) ℤ //
        IsKFlatIndependentCoefficients A}) :=
      comparison ((total R).obj K.val) (T K) (S K) (e K) (eS K) RF η
    refine ⟨⟨inferInstance, T, e, β, localizedTensorMap R,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro K
      exact ⟨localizedTensorShift R K, localizedTensor_triangulated R K⟩
    · intro K X I N s q hs hI hi hq hN hn
      let := hs
      let := hI
      let := hq
      let := hN
      obtain ⟨dI, dN, hdI, hdN, hβ⟩ := comparison_resolution
        ((total R).obj K.val) (T K) (S K) (e K) (eS K) RF η
        (fun U V f hf ↦ (tensor_quasiIso R K.val K.property f hf).1) X I N s q
      let b : ((total R).obj K.val).obj (roosP I) ⟶ roosP N :=
        productComparisonMap ((total R).obj K.val) I N q
      let θ : ((total R).obj K.val).obj (limit I.asFunctor) ⟶ limit N.asFunctor :=
        limitComparisonMap ((total R).obj K.val) I N q
      have hb := productComparisonMap_comm ((total R).obj K.val) I N q
      have hθ : ((total R).obj K.val).map (InjectiveTowerRoos.inclusion I) ≫ b =
          θ ≫ InjectiveTowerRoos.inclusion N := by
        apply Pi.hom_ext
        intro n
        dsimp only [InjectiveTowerRoos.inclusion]
        simp only [Category.assoc, Pi.lift_π]
        rw [productComparisonMap_π, ← Functor.map_comp_assoc, Pi.lift_π,
          limitComparisonMap_π]
      have hsign := signedFiberMap_spec R K.val I N b θ hb hθ
      have hcoords := hsign.1
      have hψ := hsign.2
      have hroos (V : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) [V.IsKInjective]
          (hi : ∀ k : ℤ, Injective (V.X k)) : QuasiIso (roosι V) := by
        obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _⟩ := injectiveTowerRoosShifts
          J ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
          (fun U a b ↦ @mul_comm (R.obj.obj U) inferInstance a b)
        exact (h V hi).2.2.2.2.1
      have hιI := hroos I hi
      have hιN := hroos N hn
      let := hιI
      let := hιN
      refine ⟨dI, dN, b, θ, signedFiberMap R K.val I N b hb, hdI, hdN,
        fun n ↦ productComparisonMap_π _ _ _ _ n,
        fun n ↦ limitComparisonMap_π _ _ _ _ (.op n), hcoords, hb, hψ, hβ,
        hιI, hιN, asIso (DerivedCategory.Q.map (roosι I)),
        asIso (DerivedCategory.Q.map (roosι N)), rfl, rfl, ?_⟩
      rw [hβ]
      simp only [Functor.map_comp, asIso_hom, Category.assoc]
      erw [(e K).hom.naturality_assoc (roosι I)]
      simp only [Functor.comp_map]
      rw [← DerivedCategory.Q.map_comp_assoc, hψ, DerivedCategory.Q.map_comp]
      simp only [asIso_inv, Category.assoc]
      rw [IsIso.hom_inv_id_assoc]
    · exact localizedTensorMap_fac R
    · intro K L α X
      exact comparison_naturality ((total R).obj K.val) (T K) (S K) (e K) (eS K)
        RF η ((total R).obj L.val) (T L) (S L) (e L) (eS L) ((total R).map α)
        (localizedTensorMap R K L α) (localizedTensorMap_fac R K L α)
        (fun U V f hf ↦ (tensor_quasiIso R L.val L.property f hf).1) X
    · exact localizedTensorMap_isIso R
    · intro K X Y f hf
      let := hf
      have := tower_quasiIso ((total R).obj K.val)
        (fun U V g hg ↦ (tensor_quasiIso R K.val K.property g hg).1) f hf
      exact ⟨inferInstance, inferInstance⟩
    · dsimp only
      intro K X hp
      let I := (kInjectiveResolutionFunctor.{r}
        (ℕᵒᵖ ⥤ Modules R)).obj X
      let s := (toKInjectiveResolution.{r} (ℕᵒᵖ ⥤ Modules R)).app X
      let N := (kInjectiveResolutionFunctor.{r}
        (ℕᵒᵖ ⥤ Modules R)).obj ((tower ((total R).obj K.val)).obj I)
      let q := (toKInjectiveResolution.{r} (ℕᵒᵖ ⥤ Modules R)).app
        ((tower ((total R).obj K.val)).obj I)
      let : QuasiIso s :=
        (monoQuasiIso_toKInjectiveResolution_app.{r} (ℕᵒᵖ ⥤ Modules R) X).2
      let : QuasiIso q :=
        (monoQuasiIso_toKInjectiveResolution_app.{r} (ℕᵒᵖ ⥤ Modules R)
          ((tower ((total R).obj K.val)).obj I)).2
      obtain ⟨dI, dN, _, _, hβ⟩ := comparison_resolution
        ((total R).obj K.val) (T K) (S K) (e K) (eS K) RF η
        (fun U V f hf ↦ (tensor_quasiIso R K.val K.property f hf).1) X I N s q
      have := limitComparisonMap_isIso R K.val K.property (T K) (e K) X I N s q
        (fun k ↦ inferInstance) (fun k ↦ inferInstance) hp
      change IsIso ((comparison _ _ _ _ _ RF η).app X)
      rw [hβ]
      infer_instance
    · intro K X γ
      exact comparison_augmentation ((total R).obj K.val) (T K) (S K)
        (e K) (eS K) RF η X γ

end CategoryTheory
