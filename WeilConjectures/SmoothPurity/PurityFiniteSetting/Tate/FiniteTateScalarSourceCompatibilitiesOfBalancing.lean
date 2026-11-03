/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence

/-! # Source compatibilities from finite Tate balancing

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-source-compatibilities-of-balancing)

The specified source arrow is a composite of the scalar tensorator, the canonical
scalar/pullback comparison, and the shifted line map. Coherence of the published
unit comparisons gives its coefficient-unit and zero-power equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

private theorem localTensorNaturalityLeft
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    (d : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    {P Q : C} (a : P ⟶ Q) (M : C) :
    S.map (a ▷ M) ≫ d.hom.app (Q, M) =
      d.hom.app (P, M) ≫ S.map a ▷ S.obj M := by
  have h := d.hom.naturality (show (P, M) ⟶ (Q, M) from (a, 𝟙 M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  change S.map (a ▷ M ≫ Q ◁ 𝟙 M) ≫ d.hom.app (Q, M) = _ at h
  simp only [whiskerLeft_id, Category.comp_id] at h
  change S.map (a ▷ M) ≫ d.hom.app (Q, M) =
    d.hom.app (P, M) ≫ S.map a ▷ S.obj M ≫ S.obj Q ◁ S.map (𝟙 M) at h
  rw [S.map_id, whiskerLeft_id, Category.comp_id] at h
  exact h

private def localTensorBalancing
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (P : C ⥤ D) (P' : B ⥤ E) (S : C ⥤ B) (U : D ⥤ E)
    (delta : Functor.uncurry.obj (curriedTensor D) ⋙ U ≅
      U.prod U ⋙ Functor.uncurry.obj (curriedTensor E))
    (c : S ⋙ P' ≅ P ⋙ U) (L : D) (M : E) (e : U.obj L ≅ M) :
    (P ⋙ (curriedTensor D).flip.obj L) ⋙ U ≅
      S ⋙ (P' ⋙ (curriedTensor E).flip.obj M) :=
  NatIso.ofComponents (fun K ↦ delta.app (P.obj K, L) ≪≫
    ((curriedTensor E).mapIso (c.app K).symm).app _ ≪≫
      ((curriedTensor E).obj (P'.obj (S.obj K))).mapIso e) (by
    intro K K' a
    have hd := localTensorNaturalityLeft U delta (P.map a) L
    have hc := c.inv.naturality a
    dsimp only [Functor.comp_map] at hc
    dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.comp_map, Functor.flip_obj_map, curriedTensor_obj_map,
      curriedTensor_map_app, Iso.symm_hom]
    simp only [Category.assoc]
    change U.map (P.map a ▷ L) ≫ delta.hom.app (P.obj K', L) ≫
      c.inv.app K' ▷ U.obj L ≫ P'.obj (S.obj K') ◁ e.hom =
        delta.hom.app (P.obj K, L) ≫ c.inv.app K ▷ U.obj L ≫
          P'.obj (S.obj K) ◁ e.hom ≫ P'.map (S.map a) ▷ M
    erw [reassoc_of% hd, ← comp_whiskerRight_assoc, hc,
      comp_whiskerRight_assoc, whisker_exchange])

private theorem localTensorBalancing_unit
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (P : C ⥤ D) (P' : B ⥤ E) (S : C ⥤ B) (U : D ⥤ E)
    (delta : Functor.uncurry.obj (curriedTensor D) ⋙ U ≅
      U.prod U ⋙ Functor.uncurry.obj (curriedTensor E))
    (c : S ⋙ P' ≅ P ⋙ U) (uU : U.obj (𝟙_ D) ≅ 𝟙_ E)
    (hu : ∀ L, delta.hom.app (𝟙_ D, L) ≫ uU.hom ▷ U.obj L ≫
      (λ_ (U.obj L)).hom = U.map (λ_ L).hom)
    (K : C) (K' : B) (q : S.obj K ⟶ K')
    (p : P.obj K ⟶ 𝟙_ D) (p' : P'.obj K' ⟶ 𝟙_ E)
    (hc : c.inv.app K ≫ P'.map q ≫ p' = U.map p ≫ uU.hom)
    (L : D) (M : E) (e : U.obj L ≅ M) :
    (localTensorBalancing P P' S U delta c L M e).hom.app K ≫
      ((P'.map q ≫ p') ▷ M) ≫ (λ_ M).hom =
        U.map ((p ▷ L) ≫ (λ_ L).hom) ≫ e.hom := by
  have hd := localTensorNaturalityLeft U delta p L
  simp only [localTensorBalancing, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, curriedTensor_map_app,
    curriedTensor_obj_map, U.map_comp, Category.assoc]
  change delta.hom.app (P.obj K, L) ≫ c.inv.app K ▷ U.obj L ≫
      P'.obj (S.obj K) ◁ e.hom ≫ (P'.map q ≫ p') ▷ M ≫ (λ_ M).hom = _
  erw [whisker_exchange_assoc, ← comp_whiskerRight_assoc, hc,
    comp_whiskerRight_assoc, leftUnitor_naturality, ← reassoc_of% hd,
    reassoc_of% (hu L)]

private theorem localTensorNaturalityRight
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    (d : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    (X : C) {Y Z : C} (a : Y ⟶ Z) :
    S.map (X ◁ a) ≫ d.hom.app (X, Z) =
      d.hom.app (X, Y) ≫ (S.obj X ◁ S.map a) := by
  have h := d.hom.naturality (show (X, Y) ⟶ (X, Z) from (𝟙 X, a))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  change S.map ((𝟙 X ▷ Y) ≫ X ◁ a) ≫ d.hom.app (X, Z) =
    d.hom.app (X, Y) ≫ S.map (𝟙 X) ▷ S.obj Y ≫ S.obj X ◁ S.map a at h
  rw [id_whiskerRight, Category.id_comp] at h
  rw [S.map_id, id_whiskerRight] at h
  have hi : 𝟙 (S.obj X ⊗ S.obj Y) ≫ (S.obj X ◁ S.map a) =
      S.obj X ◁ S.map a := Category.id_comp _
  rw [hi] at h
  exact h

private theorem localTensorBalancing_right_unit
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory B] [MonoidalCategory E]
    (P : C ⥤ D) (P' : B ⥤ E) (S : C ⥤ B) (U : D ⥤ E)
    (delta : Functor.uncurry.obj (curriedTensor D) ⋙ U ≅
      U.prod U ⋙ Functor.uncurry.obj (curriedTensor E))
    (c : S ⋙ P' ≅ P ⋙ U)
    (L : D) (M : E) (e : U.obj L ≅ M)
    (uL : L ≅ 𝟙_ D) (uM : M ≅ 𝟙_ E)
    (uU : U.obj (𝟙_ D) ≅ 𝟙_ E)
    (hu : ∀ K, delta.hom.app (K, 𝟙_ D) ≫
      (U.obj K ◁ uU.hom) ≫ (ρ_ (U.obj K)).hom = U.map (ρ_ K).hom)
    (he : e.hom ≫ uM.hom = U.map uL.hom ≫ uU.hom) :
    ∀ K, (localTensorBalancing P P' S U delta c L M e).hom.app K ≫
      (P'.obj (S.obj K) ◁ uM.hom) ≫ (ρ_ (P'.obj (S.obj K))).hom =
      U.map ((P.obj K ◁ uL.hom) ≫ (ρ_ (P.obj K)).hom) ≫ c.inv.app K := by
  intro K
  simp only [localTensorBalancing, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, curriedTensor_map_app,
    curriedTensor_obj_map, Category.assoc]
  have hd := localTensorNaturalityRight U delta (P.obj K) uL.hom
  change delta.hom.app (P.obj K, L) ≫ c.inv.app K ▷ U.obj L ≫
      P'.obj (S.obj K) ◁ e.hom ≫ P'.obj (S.obj K) ◁ uM.hom ≫
      (ρ_ (P'.obj (S.obj K))).hom = _
  erw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp_assoc,
    ← whisker_exchange_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  erw [← reassoc_of% hd, reassoc_of% (hu (P.obj K)), ← U.map_comp_assoc]

set_option linter.unusedVariables false in
/--
Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-source-compatibilities-of-balancing)

For a balancing family satisfying the line normalization, compose the specified
scalar tensorator, scalar/pullback comparison, and shifted line map. Each factor
is invertible for every unbounded input, so the source map is invertible. Naturality
of the scalar tensor-unit and pullback-unit comparisons, followed by cancellation
of their isomorphisms, gives the coefficient-unit equation. Transporting the
scalar right-unit equation through the degree-zero line normalization gives the
zero-power equation. These are exactly the two remaining source predicates.
-/
theorem finite_tate_scalar_source_compatibilities_of_balancing [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r)
    (hβ : IsFiniteTateScalarBalancing φ N hA hB X β)
    (hline : IsFiniteTateScalarLineNormalized φ N hA hB X β) :
    IsFiniteTateScalarSourceInvertible φ N hA hB X β ∧
      IsFiniteTateScalarSourceUnitNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceZeroNormalized φ N hA hB X β := by
  refine ⟨?_, ?_, ?_⟩
  · intro Y hY f K r
    let := hline.2.1 r
    unfold finiteTateScalarSourceMap
    infer_instance
  · intro Y hY f r
    unfold IsFiniteTateScalarLeftUnitEquation finiteTateScalarSourceMap
    simp only [Category.assoc]
    let P := L(Etale.upperStar (ModuleCat.{u + 1} A) f)
    let P' := L(Etale.upperStar (ModuleCat.{u + 1} B) f)
    let S := Etale.purityScalarExtension φ Y
    let U := Etale.purityScalarExtension φ X
    let delta := Etale.ExceptionalCoefficients.tensorIso φ X
    let c := Etale.scalarPullbackIso φ f
    let uP := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f
    let uP' := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f
    let uS := Etale.ExceptionalCoefficients.unitIso φ Y
    let := hline.2.1 r
    let uU := Etale.ExceptionalCoefficients.unitIso φ X
    let e := Iso.mk (finiteTateScalarLineMap φ N hA hB X r (β r))
      (inv (finiteTateScalarLineMap φ N hA hB X r (β r)))
      (by simp) (by simp)
    have hu : ∀ L, delta.hom.app (𝟙_ _, L) ≫ uU.hom ▷ U.obj L ≫
        (λ_ (U.obj L)).hom = U.map (λ_ L).hom := by
      intro L
      exact Etale.ExceptionalCoefficients.tensorIso_left_unit φ X L
    have hc : c.hom.app (𝟙_ _) ≫ U.map uP.hom ≫ uU.hom =
        P'.map uS.hom ≫ uP'.hom := by
      exact Etale.etaleScalarPullback_unit φ f
    let k := Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y
    let k' := Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) Y
    have hc' : c.inv.app ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≫
        P'.map (purityScalarUnitMap φ Y) ≫
        (P'.map k'.hom ≫ uP'.hom) =
        U.map (P.map k.hom ≫ uP.hom) ≫ uU.hom := by
      have hn := c.inv.naturality k.hom
      dsimp only [Functor.comp_map] at hn
      have hc0 : c.inv.app (𝟙_ _) ≫ P'.map uS.hom ≫ uP'.hom =
          U.map uP.hom ≫ uU.hom := by
        erw [← hc, c.inv_hom_id_app_assoc]
      have hq : purityScalarUnitMap φ Y ≫ k'.hom = S.map k.hom ≫ uS.hom := by
        simp only [purityScalarUnitMap, purityTransportUnitMap, Iso.symm_inv,
          Iso.symm_hom, k, k', S, uS, Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
      calc
        _ = c.inv.app _ ≫ P'.map (S.map k.hom) ≫ P'.map uS.hom ≫ uP'.hom := by
          rw [← P'.map_comp_assoc, hq, P'.map_comp]
          simp only [Category.assoc]
        _ = U.map (P.map k.hom) ≫ c.inv.app _ ≫ P'.map uS.hom ≫ uP'.hom := by
          erw [← reassoc_of% hn]
        _ = _ := by rw [hc0, U.map_comp, Category.assoc]
    have hh := localTensorBalancing_unit P P' S U delta c uU hu
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) (purityScalarUnitMap φ Y)
      (P.map k.hom ≫ uP.hom) (P'.map k'.hom ≫ uP'.hom) hc'
      (finiteTateScalarObject A N hA X r) (finiteTateScalarObject B N hB X r) e
    simpa only [P, P', S, U, delta, c, uP, uP', uS, uU, e, k, k',
      localTensorBalancing, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, curriedTensor_map_app,
      curriedTensor_obj_map, Etale.purityScalarTensor, Etale.purityScalarPullback,
      MonoidalCategory.tensorHom_def, Functor.comp_obj, Functor.flip_obj_obj,
      Functor.prod_obj, curriedTensor_obj_obj, Iso.app_inv, Category.assoc] using hh
  · intro Y hY f K
    unfold IsFiniteTateScalarRightUnitEquation finiteTateScalarSourceMap
    simp only [Category.assoc]
    let P := L(Etale.upperStar (ModuleCat.{u + 1} A) f)
    let P' := L(Etale.upperStar (ModuleCat.{u + 1} B) f)
    let S := Etale.purityScalarExtension φ Y
    let U := Etale.purityScalarExtension φ X
    let delta := Etale.ExceptionalCoefficients.tensorIso φ X
    let c := Etale.scalarPullbackIso φ f
    let uU := Etale.ExceptionalCoefficients.unitIso φ X
    let := hline.2.1 0
    let e := Iso.mk (finiteTateScalarLineMap φ N hA hB X 0 (β 0))
      (inv (finiteTateScalarLineMap φ N hA hB X 0 (β 0)))
      (by simp) (by simp)
    have hu : ∀ L, delta.hom.app (L, 𝟙_ _) ≫ U.obj L ◁ uU.hom ≫
        (ρ_ (U.obj L)).hom = U.map (ρ_ L).hom := by
      intro L
      exact Etale.ExceptionalCoefficients.tensorIso_right_unit φ X L
    have he : e.hom ≫ (finiteTateScalarZeroIso B N hB X).hom =
        U.map (finiteTateScalarZeroIso A N hA X).hom ≫ uU.hom := by
      exact hline.2.2
    have hh := localTensorBalancing_right_unit P P' S U delta c
      (finiteTateScalarObject A N hA X 0) (finiteTateScalarObject B N hB X 0) e
      (finiteTateScalarZeroIso A N hA X) (finiteTateScalarZeroIso B N hB X) uU hu he K
    simpa only [P, P', S, U, delta, c, e, finiteTateScalarSourceMap,
      Etale.purityScalarTensor, Etale.purityScalarPullback, localTensorBalancing,
      NatIso.ofComponents_hom_app,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
      curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
      Functor.comp_obj, Functor.flip_obj_obj,
      Functor.prod_obj, curriedTensor_obj_obj, Iso.app_inv, Category.assoc] using hh

end WeilConjectures.PurityFiniteSetting
