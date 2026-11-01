/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierTensorDescent
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! Coherence of the canonical tensor comparison with finite-stage inclusion. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u v w u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] WeilConjectures.CoefQbarTensor
private theorem tensor_scalar_app
    {C : Type*} [Category C] {D : Type*} [Category D]
    (U : C × C ⥤ C) (V : D × D ⥤ D) {F G : C ⥤ D} (e : F ≅ G)
    (c : U ⋙ G ≅ G.prod G ⋙ V) (K P : C) :
    (Functor.isoWhiskerLeft U e ≪≫ c ≪≫
      Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).app (K, P) =
    e.app (U.obj (K, P)) ≪≫ c.app (K, P) ≪≫
      V.mapIso (Iso.prod (e.app K).symm (e.app P).symm) := by
  apply Iso.ext
  rfl

private theorem eqIso_app_cancel
    {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (h : F = G) (X : C) (ho : F.obj X = G.obj X) :
    eqToIso ho.symm ≪≫ (eqToIso h).app X = Iso.refl _ := by
  subst G
  simp
  rfl

private theorem naturality_of_iso
    {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {A B : D}
    (a : A ≅ F.obj X) (b : B ≅ F.obj Y) (c : A ≅ G.obj X) (d : B ≅ G.obj Y)
    (ha : a ≪≫ e.app X = c) (hb : b ≪≫ e.app Y = d)
    (f : A ⟶ B) (g : X ⟶ Y) (hc : f ≫ d.hom = c.hom ≫ G.map g) :
    f ≫ b.hom = a.hom ≫ F.map g := by
  apply (cancel_mono (e.hom.app Y)).mp
  have ha' := congrArg Iso.hom ha
  have hb' := congrArg Iso.hom hb
  dsimp only [Iso.trans_hom, Iso.app] at ha' hb'
  simpa only [← ha', ← hb', Category.assoc, ← e.hom.naturality] using hc

private theorem scalar_of_iso
    {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {A B W : D}
    (a : A ≅ F.obj X) (b : B ≅ F.obj Y) (c : A ≅ G.obj X) (d : B ≅ G.obj Y)
    (ha : a ≪≫ e.app X = c) (hb : b ≪≫ e.app Y = d)
    (f : W ⟶ A) (h : W ⟶ B) (g : X ⟶ Y)
    (hc : f ≫ c.hom ≫ G.map g = h ≫ d.hom) :
    f ≫ a.hom ≫ F.map g = h ≫ b.hom := by
  apply (cancel_mono (e.hom.app Y)).mp
  have ha' := congrArg Iso.hom ha
  have hb' := congrArg Iso.hom hb
  dsimp only [Iso.trans_hom, Iso.app] at ha' hb'
  simpa only [← ha', ← hb', Category.assoc, ← e.hom.naturality] using hc

private theorem map_isoToStage
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    {S : StageSystem C} {R : StageSystem D} (F : S.Morphism R)
    (X : S.PairCategory) {j : I} (h : X.stage ≤ j) :
    F.functor.map (S.isoToStage X h).hom =
      (R.isoToStage (F.functor.obj X) h).hom ≫
        (R.ι j).map ((F.β h).hom.app X.obj) := by
  simp only [StageSystem.isoToStage, StageSystem.Morphism.functor_map_mkHom,
    StageSystem.ι_map_eq le_rfl, StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  simp only [StageSystem.Morphism.mapAt]
  change (F.β h).hom.app X.obj ≫
      (F.Φ j).map ((S.assoc h (le_refl j)).inv.app X.obj) ≫
      (F.β (le_refl j)).inv.app ((S.T h).obj X.obj) =
    (R.assoc h (le_refl j)).inv.app ((F.Φ X.stage).obj X.obj) ≫
      (R.T (le_refl j)).map ((F.β h).hom.app X.obj)
  apply (cancel_mono ((R.T (le_refl j)).map ((F.β h).inv.app X.obj))).mp
  have hc := congrArg (fun q ↦ (F.β h).hom.app X.obj ≫ q)
    (F.coh_inv h (le_refl j) X.obj)
  simpa [Category.assoc, ← Functor.map_comp] using hc

section BilinearStages
open BilinearCoefficientDescent
attribute [local implicit_reducible] StageSystem.Morphism.functor StageSystem.ι
  productSystem familyMorphism diagonal pairedObject pairedIso pairing explicitDescent output
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
  (U : Family S S S) (join : I → I → I)
  (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

private abbrev diagonalStageIso (i : I) (K P : C i) :=
  (productSystem S S).isoToStage ⟨i, (K, P)⟩ (left i i)

private def tensorStageIso (U : Family S S S) (i : I) (K P : C i) :
    (S.ι i).obj ((U.U i).obj (K, P)) ≅
      (explicitDescent U join left right).obj ((S.ι i).obj K, (S.ι i).obj P) :=
  (familyMorphism (S := S) (S₂ := S) (T := S) U).functor.mapIso (diagonalStageIso S join left i K P)

private theorem tensorStageIso_formula (U : Family S S S) (i : I) (K P : C i) :
    tensorStageIso S join left right U i K P =
      S.isoToStage ⟨i, (U.U i).obj (K, P)⟩ (left i i) ≪≫
        (S.ι (join i i)).mapIso ((U.comparison (left i i)).app (K, P)) := by
  apply Iso.ext
  exact map_isoToStage (familyMorphism (S := S) (S₂ := S) (T := S) U)
    ⟨i, (K, P)⟩ (left i i)

private theorem diagonal_stage_iso (i : I) (K P : C i) :
    (diagonal S S).map (diagonalStageIso S join left i K P).hom =
      (pairedIso S S join left right ((S.ι i).obj K, (S.ι i).obj P)).inv := by
  simp only [diagonalStageIso, StageSystem.isoToStage, diagonal_map]
  rfl

private theorem diagonal_stage_map (i : I) {K K' P P' : C i}
    (f : K ⟶ K') (g : P ⟶ P') :
    (diagonal S S).map (((productSystem S S).ι i).map (Prod.mkHom f g)) =
      Prod.mkHom ((S.ι i).map f) ((S.ι i).map g) := by
  simp only [StageSystem.ι_map_eq le_rfl, diagonal_map]
  rfl

private theorem diagonalStageIso_natural (i : I) {K K' P P' : C i}
    (f : K ⟶ K') (g : P ⟶ P') :
    (diagonalStageIso S join left i K P).hom ≫
        (pairing S S join left right).map (Prod.mkHom ((S.ι i).map f) ((S.ι i).map g)) =
      ((productSystem S S).ι i).map (Prod.mkHom f g) ≫
        (diagonalStageIso S join left i K' P').hom := by
  apply (diagonalFF S S).map_injective
  change (diagonal S S).map _ = (diagonal S S).map _
  rw [Functor.map_comp, Functor.map_comp, diagonal_stage_iso S join left right,
    diagonal_stage_iso S join left right, diagonal_stage_map S]
  change _ ≫ (diagonal S S).map ((diagonalFF S S).preimage _) = _
  rw [(diagonalFF S S).map_preimage]
  simp only [Iso.inv_hom_id_assoc]

private theorem tensorStageIso_natural (U : Family S S S) (i : I) {K K' P P' : C i}
    (f : K ⟶ K') (g : P ⟶ P') :
    (S.ι i).map ((U.U i).map (Prod.mkHom f g)) ≫ (tensorStageIso S join left right U i K' P').hom =
      (tensorStageIso S join left right U i K P).hom ≫
        (explicitDescent U join left right).map (Prod.mkHom ((S.ι i).map f) ((S.ι i).map g)) := by
  have hn := congrArg (familyMorphism (S := S) (S₂ := S) (T := S) U).functor.map
    (diagonalStageIso_natural S join left right i f g)
  simp only [Functor.map_comp, StageSystem.Morphism.functor_map_ι] at hn
  exact hn.symm

private theorem diagonalStageIso_scalar {i j : I} (h : i ≤ j) (K P : C i) :
    (diagonalStageIso S join left i K P).hom =
      ((productSystem S S).isoToStage ⟨i, (K, P)⟩ h).hom ≫
        (diagonalStageIso S join left j ((S.T h).obj K) ((S.T h).obj P)).hom ≫
        (pairing S S join left right).map
          (Prod.mkHom ((S.transIso h).hom.app K) ((S.transIso h).hom.app P)) := by
  apply (diagonalFF S S).map_injective
  change (diagonal S S).map _ = (diagonal S S).map _
  rw [Functor.map_comp, Functor.map_comp, diagonal_stage_iso S join left right,
    diagonal_stage_iso S join left right]
  change _ = _ ≫ _ ≫ (diagonal S S).map ((diagonalFF S S).preimage _)
  rw [(diagonalFF S S).map_preimage]
  simp only [Functor.comp_obj, Iso.inv_hom_id_assoc]
  rw [StageSystem.isoToStage, diagonal_map]
  change _ = (Iso.prod (S.isoToStage _ h) (S.isoToStage _ h)).hom ≫
    (Iso.prod (S.isoToStage _ h) (S.isoToStage _ h)).inv ≫ _
  simp

private theorem tensorStageIso_scalar (U : Family S S S) {i j : I} (h : i ≤ j) (K P : C i) :
    (S.ι j).map ((U.comparison h).hom.app (K, P)) ≫
        (tensorStageIso S join left right U j ((S.T h).obj K) ((S.T h).obj P)).hom ≫
        (explicitDescent U join left right).map
          (Prod.mkHom ((S.transIso h).hom.app K) ((S.transIso h).hom.app P)) =
      (S.transIso h).hom.app ((U.U i).obj (K, P)) ≫
        (tensorStageIso S join left right U i K P).hom := by
  have hn := congrArg (familyMorphism (S := S) (S₂ := S) (T := S) U).functor.map
    (diagonalStageIso_scalar S join left right h K P)
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [map_isoToStage (familyMorphism (S := S) (S₂ := S) (T := S) U) ⟨i, (K, P)⟩ h] at hn
  simp only [Category.assoc] at hn
  change (tensorStageIso S join left right U i K P).hom =
    (S.transIso h).inv.app ((U.U i).obj (K, P)) ≫ _ at hn
  rw [hn]
  simp
  rfl
end BilinearStages

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageSystem stageSystem_existsUnique)

private def tensorFamily : BilinearCoefficientDescent.Family
    (stageSystem l Ω X) (stageSystem l Ω X) (stageSystem l Ω X) := by
  letI := RationalVerdier.units D l hl X
  exact ⟨fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) X,
    fun {_ _} h ↦ rationalTensorStageComparison l Ω X h,
    rationalTensorStageComparison_coherent l Ω X⟩

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedTensor sfRationalScalarExtension rationalTensorScalarComparison

private def tensorModel :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ×
      generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  BilinearCoefficientDescent.explicitDescent (tensorFamily D l hl Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage tensorFamily
  BilinearCoefficientDescent.explicitDescent BilinearCoefficientDescent.output
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.uniformProd
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory

private theorem tensor_model_eq : CoefQbarTensor D l hl Ω X = tensorModel D l hl Ω X := by
  let := RationalVerdier.units D l hl X
  have hs := tensor_descent_spec D l hl Ω X
  exact (BilinearCoefficientDescent.descent_existsUnique (tensorFamily D l hl Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)).unique hs
      (BilinearCoefficientDescent.explicitDescent_spec (tensorFamily D l hl Ω X)
        (Padic.finiteCoefficientCompositum l Ω)
        (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
        (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2))

private theorem tensor_inclusion_model (E : Index l Ω) (K P : Stage l Ω X E) :
    tensorInclusion D l hl Ω X E K P ≪≫
      (eqToIso (tensor_model_eq D l hl Ω X)).app ((inclusion E).obj K, (inclusion E).obj P) =
    tensorStageIso (C := Stage l Ω X) (stageSystem l Ω X)
      (Padic.finiteCoefficientCompositum l Ω)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
      (tensorFamily D l hl Ω X) E K P := by
  let := RationalVerdier.units D l hl X
  let S := stageSystem l Ω X
  let J := Padic.finiteCoefficientCompositum l Ω E E
  let h := ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1
  let Q := ((inclusion E).obj K, (inclusion E).obj P)
  have ho := congrArg (fun F ↦ F.obj Q) (tensor_model_eq D l hl Ω X)
  have hb := tensor_scalar_app (C := Stage l Ω X E) (D := Stage l Ω X J)
    (rationalDerivedTensor l (Coefficient.{u} l Ω E) X)
    (rationalDerivedTensor l (Coefficient.{u} l Ω J) X)
    (operationStageTransitionIso l Ω X E J h)
    (rationalTensorScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω J)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E J h) X) K P
  change (rationalTensorStageComparison l Ω X h).app (K, P) = _ at hb
  have hi := congrArg (fun c :
      (S.T h).obj ((rationalDerivedTensor l (Coefficient.{u} l Ω E) X).obj (K, P)) ≅
        (rationalDerivedTensor l (Coefficient.{u} l Ω J) X).obj
          ((S.T h).obj K, (S.T h).obj P) ↦ (S.transIso h).symm.app
      ((rationalDerivedTensor l (Coefficient.{u} l Ω E) X).obj (K, P)) ≪≫
      (inclusion J).mapIso c ≪≫ eqToIso ho.symm) hb.symm
  have hi' : tensorInclusion D l hl Ω X E K P =
      (S.transIso h).symm.app _ ≪≫
        (inclusion J).mapIso ((rationalTensorStageComparison l Ω X h).app (K, P)) ≪≫
          eqToIso ho.symm := hi
  let v := (S.transIso h).symm.app
      ((rationalDerivedTensor l (Coefficient.{u} l Ω E) X).obj (K, P)) ≪≫
    (inclusion J).mapIso ((rationalTensorStageComparison l Ω X h).app (K, P))
  have hcancel : (eqToIso ho.symm) ≪≫
      (eqToIso (tensor_model_eq D l hl Ω X)).app Q = Iso.refl _ :=
    eqIso_app_cancel (tensor_model_eq D l hl Ω X) Q ho
  have hv : v = tensorStageIso (C := Stage l Ω X) S
      (Padic.finiteCoefficientCompositum l Ω)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
      (tensorFamily D l hl Ω X) E K P := by
    exact (tensorStageIso_formula (C := Stage l Ω X) S
      (Padic.finiteCoefficientCompositum l Ω)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
      (tensorFamily D l hl Ω X) E K P).symm
  calc
    _ = (v ≪≫ eqToIso ho.symm) ≪≫
        (eqToIso (tensor_model_eq D l hl Ω X)).app Q :=
      congrArg (fun e ↦ e ≪≫ (eqToIso (tensor_model_eq D l hl Ω X)).app Q)
        (by simpa only [v, Iso.trans_assoc] using hi')
    _ = v ≪≫ (eqToIso ho.symm ≪≫
        (eqToIso (tensor_model_eq D l hl Ω X)).app Q) := Iso.trans_assoc _ _ _
    _ = v := (congrArg (fun e ↦ v ≪≫ e) hcancel).trans (Iso.trans_refl v)
    _ = _ := hv

attribute [local irreducible] tensorStageIso tensorInclusion

private theorem tensor_inclusion_natural (E : Index l Ω) {K K' P P' : Stage l Ω X E}
    (f : K ⟶ K') (g : P ⟶ P') :
    (inclusion E).map
        ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map (Prod.mkHom f g)) ≫
        (tensorInclusion D l hl Ω X E K' P').hom =
      (tensorInclusion D l hl Ω X E K P).hom ≫
        (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom ((inclusion E).map f) ((inclusion E).map g)) := by
  let e := eqToIso (tensor_model_eq D l hl Ω X)
  have hn := tensorStageIso_natural (C := Stage l Ω X) (stageSystem l Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
    (tensorFamily D l hl Ω X) E f g
  exact naturality_of_iso e _ _ _ _
    (tensor_inclusion_model D l hl Ω X E K P)
    (tensor_inclusion_model D l hl Ω X E K' P') _ _ hn

private theorem tensor_inclusion_scalar
    {E L : Index l Ω} (h : E ≤ L) (K P : Stage l Ω X E) :
    let := RationalVerdier.units D l hl X
    (inclusion L).map ((rationalTensorStageComparison l Ω X h).hom.app (K, P)) ≫
        (tensorInclusion D l hl Ω X L
          (((stageSystem l Ω X).T h).obj K) (((stageSystem l Ω X).T h).obj P)).hom ≫
        (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom (((stageSystem l Ω X).transIso h).hom.app K)
            (((stageSystem l Ω X).transIso h).hom.app P)) =
      ((stageSystem l Ω X).transIso h).hom.app
          ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).obj (K, P)) ≫
        (tensorInclusion D l hl Ω X E K P).hom := by
  let := RationalVerdier.units D l hl X
  let e := eqToIso (tensor_model_eq D l hl Ω X)
  have hn := tensorStageIso_scalar (C := Stage l Ω X) (stageSystem l Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
    (tensorFamily D l hl Ω X) h K P
  exact scalar_of_iso e _ _ _ _
    (tensor_inclusion_model D l hl Ω X L
      (((stageSystem l Ω X).T h).obj K) (((stageSystem l Ω X).T h).obj P))
    (tensor_inclusion_model D l hl Ω X E K P) _ _ _ hn

/-- The prescribed tensor inclusions are natural and commute with coefficient extension.
Source: blueprint thm-coef-qbar-verdier, finite-origin evaluation descent.
(blueprint: lem-coef-qbar-tensor-inclusion-coherent).
Proof: realize bilinear descent using the fully faithful diagonal of the product
stage system. The stage inclusion is the image of isoToStage. Functoriality gives
naturality; composition of isoToStage with a further stage and the pairing
isomorphism gives the coefficient square. The unique representative prescription
identifies this explicit descent with CoefQbarTensor. Unfolding the normalized
coefficient comparison identifies its stage isomorphism with tensorInclusion. -/
theorem tensorInclusion_coherent :
    (∀ (E : Index l Ω) {K K' P P' : Stage l Ω X E} (f : K ⟶ K') (g : P ⟶ P'),
      (inclusion E).map
          ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map (Prod.mkHom f g)) ≫
          (tensorInclusion D l hl Ω X E K' P').hom =
        (tensorInclusion D l hl Ω X E K P).hom ≫
          (CoefQbarTensor D l hl Ω X).map
            (Prod.mkHom ((inclusion E).map f) ((inclusion E).map g))) ∧
    (∀ {E L : Index l Ω} (h : E ≤ L) (K P : Stage l Ω X E),
      let := RationalVerdier.units D l hl X
      (inclusion L).map ((rationalTensorStageComparison l Ω X h).hom.app (K, P)) ≫
          (tensorInclusion D l hl Ω X L
            (((stageSystem l Ω X).T h).obj K) (((stageSystem l Ω X).T h).obj P)).hom ≫
          (CoefQbarTensor D l hl Ω X).map
            (Prod.mkHom (((stageSystem l Ω X).transIso h).hom.app K)
              (((stageSystem l Ω X).transIso h).hom.app P)) =
        ((stageSystem l Ω X).transIso h).hom.app
            ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).obj (K, P)) ≫
          (tensorInclusion D l hl Ω X E K P).hom) := by
  exact ⟨fun E _ _ _ _ f g ↦ tensor_inclusion_natural D l hl Ω X E f g,
    fun {_ _} h K P ↦ tensor_inclusion_scalar D l hl Ω X h K P⟩

end WeilConjectures.CoefQbarVerdier
