/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.SfIntegralConstructible
import all Sheaf.Paper.CompletedTowerDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import all Sheaf.Paper.SfDerivedDirectImage
import all Sheaf.Paper.AdicFiniteExchangeEncoding
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.Triangulated.DerivedLimitMorphism
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism

/-! # The completed finite-image tower computes ordinary direct image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
variable (h : T ⟶ U)
  (sT : RealizationScalarFunctorData l E T) (sU : RealizationScalarFunctorData l E U)


private theorem derived_preserves_products
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : ℕ → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : ℕ) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    have hqFan := HomotopyCategory.isLimitFanQuotient A (.up ℤ)
      (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I))
    have : CochainComplex.IsKInjective P.pt := by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal]
      exact (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal.prop_of_isLimit
        hqFan (fun j ↦ CochainComplex.IsKInjective.rightOrthogonal (I j.as))
    have hPL : IsLimit (DerivedCategory.Q.mapCone P) :=
      isLimitOfPreserves DerivedCategory.Q
        (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I))
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun n ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c) (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _

private theorem map_roos
    {A B : Type*} [Category A] [Category B]
    [HasZeroObject A] [HasZeroObject B] [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive]
    [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated A] [Pretriangulated B]
    (F : A ⥤ B) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {M : ℕ → A} [HasProduct M] [HasProduct (fun n ↦ F.obj (M n))]
    [PreservesLimit (Discrete.functor M) F]
    (f : ∀ n, M (n + 1) ⟶ M n) (K : A) (p : K ⟶ ∏ᶜ M)
    (δ : ∏ᶜ M ⟶ K⟦(1 : ℤ)⟧) (h : IsDerivedLimitTriangle f K p δ) :
    IsDerivedLimit (K := fun n ↦ F.obj (M n)) (fun n ↦ F.map (f n)) (F.obj K) := by
  let e := PreservesProduct.iso F M
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n ↦ F.obj (M n)) n = F.map (Pi.π M n) :=
    piComparison_comp_π F M n
  have hc : F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ F.map (f n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, Functor.map_sub,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id,
      towerProductShift, Pi.lift_π]
    rw [← Category.assoc, he]
    simp only [← F.map_comp, Pi.lift_π, Category.id_comp]
  refine ⟨F.map p ≫ e.hom,
    e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ h)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · change (F.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map p
    simp
  · change towerTransitionEndomorphism (fun n ↦ F.map (f n)) ≫ e.inv =
      e.inv ≫ F.map (towerTransitionEndomorphism f)
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← hc]
    simp
  · change (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
      (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
        e.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
    simp

private theorem detailed_image
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T))
    (hK : IsSfDerivedComplete l E T K)
    [HasProduct (sfDirectImageTerm l E h K)] (L : SfIntegralDirectImage l E h K) :
    Nonempty ((sfCompletedDerivedDirectImage l E h).obj K ≅ L.obj) := by
  classical
  let A := scalarReductionSource.{u, u} l E T
  let B := scalarReductionSource.{u, u} l E U
  letI : HasCountableProducts A := (ProEt.countableProducts_exact.{u, u, 0} T
    (completedIntegralCommRingSheafUnrestricted l E T)).1
  letI : HasCountableProducts B := (ProEt.countableProducts_exact.{u, u, 0} U
    (completedIntegralCommRingSheafUnrestricted l E U)).1
  letI : HasExactLimitsOfShape (Discrete ℕ) A := ProEt.products_exact.{u, u, 0} T _ ℕ
  letI : HasExactLimitsOfShape (Discrete ℕ) B := ProEt.products_exact.{u, u, 0} U _ ℕ
  letI : HasCountableProducts (DerivedCategory A) :=
    ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete A I⟩
  letI : HasCountableProducts (DerivedCategory B) :=
    ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete B I⟩
  let F := sfCompletedModuleDirectImage l E h
  let G := sfCompletedDerivedDirectImage l E h
  let R := completedIntegralCoefficientSheafUnrestricted l E U
  let S := completedIntegralCoefficientSheafUnrestricted l E T
  let V := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj
  let W := SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj
  letI : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ V) := by
    have e : F ⋙ V ≅ W ⋙ (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (proEtaleBaseChange h).op := Iso.refl _
    exact preservesLimitsOfShape_of_natIso e.symm
  letI : ReflectsLimitsOfShape (Discrete ℕ) V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  letI : PreservesLimitsOfShape (Discrete ℕ) F :=
    preservesLimitsOfShape_of_reflects_of_preserves F V
  letI : PreservesLimitsOfShape (Discrete ℕ) G := derived_preserves_products F
  obtain ⟨hp, δ, hδ⟩ := hK
  letI := hp
  let M (n : ℕ) := G.obj ((sfDerivedReductionRestricted l E T n).obj K)
  let d (n : ℕ) := G.map ((sfDerivedReductionTransition l E T n).app K)
  obtain ⟨p, b, hb⟩ := map_roos G _ K _ δ hδ
  let e (n : ℕ) : M n ≅ sfDirectImageTerm l E h K n :=
    (sfDerivedRestrictionComparison l E h n).app
      ((scalarReductionDerivedExtension l E T n).obj K)
  let φ : Functor.ofOpSequence (X := M) d ⟶
      Functor.ofOpSequence (sfDirectImageTransition l E h K) :=
    NatTrans.ofOpSequence (F := Functor.ofOpSequence (X := M) d)
      (G := Functor.ofOpSequence (sfDirectImageTransition l E h K)) (fun n ↦ (e n).hom) (by
      intro n
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      change d n ≫ (e n).hom = (e (n + 1)).hom ≫
        ((e (n + 1)).inv ≫ d n ≫ (e n).hom)
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp])
  obtain ⟨ψ, hψ, hψb⟩ := exists_derivedLimit_morphism d
    (sfDirectImageTransition l E h K) (G.obj K) L.obj p L.projection b L.boundary hb L.roos φ
  letI : ∀ n, IsIso (φ.app (op n)) := fun n ↦ by
    change IsIso (e n).hom
    infer_instance
  have hi := isIso_derivedLimit_of_levelwise d (sfDirectImageTransition l E h K)
    (G.obj K) L.obj p L.projection b L.boundary hb L.roos
    (fun n ↦ φ.app (op n))
    (fun n ↦ by
      simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
        φ.naturality (homOfLE (Nat.le_succ n)).op)
    ψ hψ hψb
  exact ⟨asIso ψ⟩

private theorem finite_detailed_square (n : ℕ) :
    (adicLisseForget U).map
        (proEtaleRingDirectImageMap h _ _
          (asIso (completedFiniteCoefficientMap h (pbcIntegralDatum l E) n))) ≫
      (proEtaleSheafDirectImage h RingCat.{u + 1}).map
        (integralDetailedLevelComparison T l E n).hom =
    (integralDetailedLevelComparison U l E n).hom ≫
      (adicLisseForget U).map
        (proEtaleCoefficientDirectImageMap h (Padic.coefficientExtensionRing l E (n + 1))) := by
  let e := (integralCoefficientULift l E n).toCommRingCatIso
  have hn := constantDirectImage_naturality h _ _ e.hom
  have hc : proEtaleRingDirectImageMap h _ _
        (asIso (completedFiniteCoefficientMap h (pbcIntegralDatum l E) n)) ≫
      (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
        ((pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
          (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map e.hom) =
    ((pbcLevelConstantComparison U (pbcIntegralDatum l E) n).inv ≫
      (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map e.hom) ≫
      proEtaleCoefficientDirectImageMap h (Padic.coefficientExtensionRing l E (n + 1)) := by
    let R := proEtaleSheafDirectImage h CommRingCat.{u + 1}
    change _ = _ at hn
    rw [finiteDirectImage_adjunct]
    simp only [Functor.map_comp, Category.assoc]
    have hx : R.map (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom ≫
        R.map (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv = 𝟙 _ := by
      rw [← R.map_comp, Iso.hom_inv_id, R.map_id]
    change (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).inv ≫
      proEtaleConstantDirectImageMap h CommRingCat.{u + 1} _ ≫
      R.map (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom ≫
      R.map (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
      R.map ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map e.hom) = _
    rw [← Category.assoc (R.map _) (R.map _) (R.map _), hx, Category.id_comp]
    exact congrArg
      (fun z ↦ (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).inv ≫ z) hn.symm
  apply Sheaf.hom_ext
  ext V a
  exact congrArg (fun z ↦ (z.hom.app V).hom a) hc

private theorem detailed_map_square :
    (adicLisseForget U).map (completedCoefficientDirectImageMap h (pbcIntegralDatum l E)) ≫
      (proEtaleSheafDirectImage h RingCat.{u + 1}).map
        (integralDetailedCoefficientComparison T l E).hom =
    (integralDetailedCoefficientComparison U l E).hom ≫
      (adicLisseForget U).map (sfCompletedCoefficientMap l E h) := by
  let R := proEtaleSheafDirectImage h RingCat.{u + 1}
  apply (isLimitOfPreserves R (limit.isLimit (integralCoefficientSheafSystem l E T))).hom_ext
  intro ⟨n⟩
  have hT := (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec n
  have hU := (integralDetailedCoefficientComparison_exists U l E).exists.choose_spec n
  change (integralDetailedCoefficientComparison T l E).hom ≫
    limit.π (integralCoefficientSheafSystem l E T) (op n) = _ at hT
  change (integralDetailedCoefficientComparison U l E).hom ≫
    limit.π (integralCoefficientSheafSystem l E U) (op n) = _ at hU
  have hs := (sfCompletedCoefficientMap_existsUnique l E h).exists.choose_spec n
  have ha := completedCoefficient_projection h (pbcIntegralDatum l E) n
  have ha' := congrArg
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) ha
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at ha'
  change completedCoefficientDirectImageMap h (pbcIntegralDatum l E) ≫
      (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
        (pbcAdicProjection T (pbcIntegralDatum l E) n) =
    pbcAdicProjection U (pbcIntegralDatum l E) n ≫
      proEtaleRingDirectImageMap h _ _
        (asIso (completedFiniteCoefficientMap h (pbcIntegralDatum l E) n)) at ha'
  have haR := congrArg (fun z ↦ (adicLisseForget U).map z) ha'
  have hsR := congrArg (fun z ↦ (adicLisseForget U).map z) hs
  simp only [Functor.map_comp] at haR hsR
  change _ ≫ R.map (limit.π (integralCoefficientSheafSystem l E T) (op n)) =
    _ ≫ R.map (limit.π (integralCoefficientSheafSystem l E T) (op n))
  change _ = _ at haR hsR
  erw [Category.assoc, ← R.map_comp, hT, R.map_comp, ← Category.assoc, haR]
  change ((adicLisseForget U).map (pbcAdicProjection U (pbcIntegralDatum l E) n) ≫
    (adicLisseForget U).map (proEtaleRingDirectImageMap h _ _
      (asIso (completedFiniteCoefficientMap h (pbcIntegralDatum l E) n)))) ≫
      R.map (integralDetailedLevelComparison T l E n).hom = _
  rw [Category.assoc, finite_detailed_square]
  erw [← Category.assoc, ← hU, Category.assoc]
  exact congrArg (fun z ↦ (integralDetailedCoefficientComparison U l E).hom ≫ z) hsR.symm

/-- Ordinary completed-coefficient image is the specified finite-image Roos limit.
Source: Stacks Tags 099N(3),(4), 0944 and 0D6E; Bhatt--Scholze,
Lemmas 6.5.9(2) and 6.5.11(3).
(blueprint: lem-weil-pbc-realization-completed-image)

Proof: the normalized completed coefficient comparison identifies every quotient
projection with the detailed positive-level comparison. Restriction along it is
an exact equivalence. The scalar tensor adjunction identifies the corresponding
derived reduction units and transition maps on flat K-flat representatives.
Completeness of K identifies it, with its augmentation, with the derived limit
of these reductions. Apply ordinary direct image. The normalized strict-tower
comparison with derived limits identifies the resulting limit with the tower
of images. Ringed-topos composition identifies its finite terms with the
restricted finite direct images, and its normalization on K-injective models
identifies the maps with sfDerivedRestrictionComparison. Thus the resulting
transition is exactly sfDirectImageTransition, not an arbitrary levelwise
comparison. Both this limit and L are fibres of the same one-minus-shift map
on the product. Rotate their triangles and extend the identity of the two
product vertices by the triangle axiom; the triangle five lemma makes the
first-vertex map invertible. Apply the coefficient equivalence and its counit
to obtain the assertion. No geometric base or constructibility assumption is
used; the argument includes zero complexes and empty schemes. -/
theorem realizationCompletedImage
    (cA : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (pbcAdicCompletion U (pbcIntegralDatum l E)) ≅
        pbcAdicCompletion T (pbcIntegralDatum l E))
    (hcA : cA.hom = completedCoefficientMap h (pbcIntegralDatum l E))
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T))
    (hK : IsSfDerivedComplete l E T K)
    [HasProduct (sfDirectImageTerm l E h K)] (L : SfIntegralDirectImage l E h K) :
    Nonempty ((proEtaleRingDerivedDirectImage h _ _ cA).obj
        ((integralDetailedTransport T l E).obj K) ≅
      (integralDetailedTransport U l E).obj L.obj) := by
  classical
  letI : Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E T)) :=
    sfCompletedHasKInjectiveResolutions l E T
  letI : Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E U)) :=
    sfCompletedHasKInjectiveResolutions l E U
  let R := proEtaleSheafDirectImage h RingCat.{u + 1}
  let eT := integralDetailedCoefficientComparison T l E
  let eU := integralDetailedCoefficientComparison U l E
  let P := SheafOfModules.restrictScalars.{u + 1} eT.hom
  let Q := SheafOfModules.restrictScalars.{u + 1} eU.hom
  let F := sfCompletedModuleDirectImage l E h
  let G := proEtaleRingModuleDirectImage h _ _ cA
  letI : P.Additive := inferInstanceAs (SheafOfModules.restrictScalars eT.hom).Additive
  letI : Q.Additive := inferInstanceAs (SheafOfModules.restrictScalars eU.hom).Additive
  letI : P.IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence T eT).functor.IsEquivalence
  letI : F.Additive := sfCompletedModuleDirectImage_additive l E h
  letI : PreservesFiniteLimits P := (integralDetailedCoefficientRestriction_exact T l E).1
  letI : PreservesFiniteColimits P := (integralDetailedCoefficientRestriction_exact T l E).2
  letI : PreservesFiniteLimits Q := (integralDetailedCoefficientRestriction_exact U l E).1
  letI : PreservesFiniteColimits Q := (integralDetailedCoefficientRestriction_exact U l E).2
  have hs : (adicLisseForget U).map (proEtaleRingDirectImageMap h _ _ cA) ≫
      R.map eT.hom = eU.hom ≫ (adicLisseForget U).map (sfCompletedCoefficientMap l E h) := by
    rw [proEtaleRingDirectImageMap, hcA]
    exact detailed_map_square l E h
  let z : P ⋙ G ≅ F ⋙ Q := NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom
            (X := ((P ⋙ G).obj M).val.obj V) (Y := ((F ⋙ Q).obj M).val.obj V)
            { toFun := id
              map_add' := fun _ _ ↦ rfl
              map_smul' := by
                intro r x
                change ((eT.hom.hom.app ((proEtaleBaseChange h).op.obj V)).hom
                    ((proEtaleRingDirectImageMap h _ _ cA).hom.app V r)) •
                    (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x) =
                  ((sfCompletedCoefficientMap l E h).hom.app V (eU.hom.hom.app V r)) •
                    (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x)
                exact congrArg (fun a : (completedIntegralCoefficientSheafUnrestricted
                    l E T).obj.obj ((proEtaleBaseChange h).op.obj V) ↦
                  a • (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x))
                  (congrArg (fun z ↦ (z.hom.app V).hom r) hs) }
          inv := ModuleCat.ofHom
            (X := ((F ⋙ Q).obj M).val.obj V) (Y := ((P ⋙ G).obj M).val.obj V)
            { toFun := id
              map_add' := fun _ _ ↦ rfl
              map_smul' := by
                intro r x
                change ((sfCompletedCoefficientMap l E h).hom.app V (eU.hom.hom.app V r)) •
                    (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x) =
                  ((eT.hom.hom.app ((proEtaleBaseChange h).op.obj V)).hom
                    ((proEtaleRingDirectImageMap h _ _ cA).hom.app V r)) •
                    (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x)
                exact congrArg (fun a : (completedIntegralCoefficientSheafUnrestricted
                    l E T).obj.obj ((proEtaleBaseChange h).op.obj V) ↦
                  a • (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x))
                  (congrArg (fun z ↦ (z.hom.app V).hom r) hs).symm }
          hom_inv_id := by ext; rfl
          inv_hom_id := by ext; rfl })
        (by intros; ext; rfl))) (by intros; ext; rfl)
  let d : P.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ Q.mapDerivedCategory :=
    (Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory _).symm ≪≫
      (Functor.rightDerivedFunctorCompIso P G).symm ≪≫
      Functor.rightDerivedFunctorNatIso z ≪≫
      Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q
  obtain ⟨e⟩ := detailed_image l E h K hK L
  exact ⟨d.app K ≪≫ Q.mapDerivedCategory.mapIso e⟩

end WeilConjectures
