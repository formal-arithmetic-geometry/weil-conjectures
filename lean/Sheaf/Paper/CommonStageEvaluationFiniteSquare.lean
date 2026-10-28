/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.CommonStageInclusionTensorComparison
public import Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA

/-! # Finite-stage normalization of common-stage evaluation

Source: Bhatt--Scholze, Lemma 3.4.11 and Proposition 6.8.14; the finite-stage
square in step 7 of lem-sf-adic-ambient-hom-evaluation-comparison.
The module also proves the generic adjunction, symmetry, and transition calculations
used to realize that square and assemble the coherence laws.
(blueprint: lem-sf-common-stage-evaluation-finite-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The chosen common-stage internal Hom has its prescribed literal object.
This is the object clause of its defining unique-existence theorem.
Source: the common-stage Hom construction in def-weil-derived-pullback-tensor-hom. -/
theorem commonStageDerivedInternalHom_obj_eq
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (P : (commonStageHomPairs l Ω X).FullSubcategory) :
    (commonStageDerivedInternalHom l Ω X).obj P = commonStageHomObject l Ω X P := by
  unfold commonStageDerivedInternalHom
  exact (commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 P

attribute [local irreducible] commonStageDerivedInternalHom

/-- The common-stage evaluation is the included rational evaluation under the
specified Hom, input, and output scalar identifications.

Source: BS Lemma 3.4.11 and Proposition 6.8.14; step 7 of the ambient comparison.
(blueprint: lem-sf-common-stage-evaluation-finite-square).

Proof: evaluation is inverse transposition of the identity of the common Hom.
Transport along the recorded literal Hom-object equality and represent that
identity at F. The Hom stage is the compositum of the entry stages, so F also
contains both entries and the tensor of the Hom with the first
entry. Apply PodCommonTransposeNormalization at F.
The inverse rational transpose of the identity is rational evaluation; its
naturality in the test object moves the specified rational Hom comparison to
the first tensor input. The normalization of stageTensor identifies the tensor
comparison with the inverse inclusion tensorator, including the normalized
reflexive scalar units in stageTensorFormula. Cancel adjacent inverse comparison
factors only after inserting those units. The isoToStage maps give the other
two entry identifications. Functoriality of the common-stage tensor,
using its representative formula at F, identifies the resulting representative
with the left side of the square. Thus the two arrows have equal representatives
at F; no faithfulness of the finite-stage inclusion is assumed. Identity
extensions, zero objects, and empty schemes use the same normalization. -/
theorem commonStageEvaluation_finiteSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (S : PodPartialClosed (commonStageDerivedTensor l Ω X)
      (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X))
    (hS : PodCommonTransposeNormalization l Ω X S)
    (P : (commonStageHomPairs l Ω X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageHomObject l Ω X P).stage ≤ F) :
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) F
    let Q := commonStageHomPairAtStage l Ω X P F h
    let γH := eqToIso (commonStageDerivedInternalHom_obj_eq l Ω X P)
      ≪≫ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
        (commonStageHomObject l Ω X P) h ≪≫
      I.mapIso (commonStageHomComparison l Ω X P F h)
    let γM := (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
      P.obj.1.unop (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)
    let γN := (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
      P.obj.2 (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h)
    (commonStageDerivedTensor l Ω X).map (Prod.mkHom γH.hom γM.hom) ≫
        (AdicQbarRealization.stageTensor l X Ω F
          ((rationalDerivedInternalHom l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X).obj Q)
          Q.obj.1.unop).inv ≫
        I.map ((podRationalClosed l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X).evaluation Q) =
      S.evaluation P ≫ γN.hom := by sorry

namespace AdicQbarRealization.AmbientHomEvaluation.CoherenceCalculus

/-- Inverse transposition is tensoring with the map followed by evaluation. -/
lemma uncurry
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (X K M : C)
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X K M).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ S.evaluation K M := by
  let := S.monoidal
  change ((S.adjunction K).homEquiv X M).symm f = _
  simp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id]
  rfl

/-- Inverse transposition is natural in the test object. -/
lemma uncurry_precomp
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (X X' K M : C) (a : X' ⟶ X)
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X' K M).symm (a ≫ f) =
      S.tensor.map (Prod.mkHom a (𝟙 K)) ≫ (S.transpose X K M).symm f := by
  rw [uncurry, uncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id]

/-- Evaluation is natural in its contravariant and covariant entries. -/
lemma evaluation_pair
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (M M' N N' : C) (f : M' ⟶ M) (g : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 M')) ≫
        S.evaluation M' N' =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op M, N))) f) ≫ S.evaluation M N ≫ g := by
  let := S.monoidal
  have hf := S.evaluation_naturality M M' N f
  have hg := (S.adjunction M').counit.naturality g
  have hp : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op M')) g) := by
    rw [← H.map_comp]
    simp only [CategoryTheory.prod_comp, Category.comp_id, Category.id_comp]
  rw [hp]
  simp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] at *
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
  change MonoidalCategoryStruct.whiskerRight
    (H.map (Prod.mkHom (𝟙 (op M')) g)) M' ≫ (S.adjunction M').counit.app N' =
      (S.adjunction M').counit.app N ≫ g at hg
  change MonoidalCategoryStruct.whiskerRight
    (H.map (Prod.mkHom f.op (𝟙 N))) M' ≫ (S.adjunction M').counit.app N =
      MonoidalCategoryStruct.whiskerLeft (H.obj (op M, N)) f ≫
        (S.adjunction M).counit.app N at hf
  rw [hg, ← Category.assoc, hf, Category.assoc]

/-- Inverse transposition is natural in both entries of internal Hom. -/
lemma uncurry_postcomp
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (X M M' N N' : C)
    (a : X ⟶ H.obj (op M, N)) (f : M' ⟶ M) (g : N ⟶ N') :
    (S.transpose X M' N').symm (a ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 X) f) ≫ (S.transpose X M N).symm a ≫ g := by
  rw [uncurry, uncurry]
  have h := congrArg (fun k ↦ S.tensor.map (Prod.mkHom a (𝟙 M')) ≫ k)
    (evaluation_pair S M M' N N' f g)
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using h

/-- Tensorator naturality carries a source evaluation square to its realization. -/
lemma realized_evaluation_square
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (μ : (F.prod F) ⋙ U ≅ T ⋙ F)
    {K M N K' M' N' V : C} (gK : K ≅ K') (gM : M ≅ M') (gN : N ≅ N')
    (e : T.obj (K, M) ⟶ N) (a : T.obj (K', M') ⟶ V) (b : V ⟶ N')
    (he : T.map (Prod.mkHom gK.hom gM.hom) ≫ a ≫ b = e ≫ gN.hom) :
    U.map (Prod.mkHom (F.mapIso gK).hom (F.mapIso gM).hom) ≫
        μ.hom.app (K', M') ≫ F.map a ≫ F.map b =
      (μ.hom.app (K, M) ≫ F.map e) ≫ (F.mapIso gN).hom := by
  have hn := μ.hom.naturality (Prod.mkHom gK.hom gM.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ← F.map_comp,
    he, F.map_comp]

/-- A tensorator symmetry equation remains valid after evaluation. -/
lemma realized_braiding_evaluation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B N : C} {U V : D} (d : U ⟶ V) (μ : V ⟶ F.obj A) (ν : U ⟶ F.obj B)
    (b : B ⟶ A) (e : A ⟶ N) (h : d ≫ μ = ν ≫ F.map b) :
    d ≫ (μ ≫ F.map e) = ν ≫ F.map (b ≫ e) := by
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp]

/-- An evaluation square gives the corresponding square between its transposes. -/
lemma comparison_square
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (U M N U' M' N' : C)
    (v : S.tensor.obj (U, M) ⟶ N) (v' : S.tensor.obj (U', M') ⟶ N')
    (gU : U ≅ U') (gM : M ≅ M') (gN : N ≅ N')
    (hv : S.tensor.map (Prod.mkHom gU.hom gM.hom) ≫ v' = v ≫ gN.hom) :
    gU.hom ≫ S.transpose _ _ _ v' =
      S.transpose _ _ _ v ≫ H.map (Prod.mkHom gM.inv.op gN.hom) := by
  apply (S.transpose _ _ _).symm.injective
  rw [uncurry_precomp, uncurry_postcomp,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have he := congrArg (fun k ↦ S.tensor.map (Prod.mkHom (𝟙 U) gM.inv) ≫ k) hv
  simpa only [← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp, Iso.inv_hom_id, Functor.map_id, Category.assoc] using he

/-- Braiding naturality converts right evaluation into left evaluation. -/
lemma braiding_evaluation
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (B : @SymmetricCategory C _ S.monoidal)
    (K M N : C) (a : K ⟶ H.obj (op M, N)) (v : S.tensor.obj (K, M) ⟶ N)
    (hv : S.tensor.map (Prod.mkHom a (𝟙 M)) ≫ S.evaluation M N = v) :
    S.tensor.map (Prod.mkHom (𝟙 M) a) ≫ (B.braiding M (H.obj (op M, N))).hom ≫
        S.evaluation M N = (B.braiding M K).hom ≫ v := by
  let := S.monoidal
  let := B
  have hb : S.tensor.map (Prod.mkHom (𝟙 M) a) ≫
        (B.braiding M (H.obj (op M, N))).hom =
      (B.braiding M K).hom ≫ S.tensor.map (Prod.mkHom a (𝟙 M)) :=
    BraidedCategory.braiding_naturality (𝟙 M) a
  rw [← Category.assoc, hb, Category.assoc, hv]

/-- Two comparison squares give compatibility with conjugated transitions. -/
lemma comparison_extension
    {C : Type*} [Category C] (H : Cᵒᵖ × C ⥤ C)
    {U M N UF MF NF UG MG NG : C}
    (uF : U ≅ UF) (mF : M ≅ MF) (nF : N ≅ NF)
    (uG : U ≅ UG) (mG : M ≅ MG) (nG : N ≅ NG)
    (c : U ⟶ H.obj (op M, N)) (cF : UF ⟶ H.obj (op MF, NF))
    (cG : UG ⟶ H.obj (op MG, NG))
    (hF : uF.hom ≫ cF = c ≫ H.map (Prod.mkHom mF.inv.op nF.hom))
    (hG : uG.hom ≫ cG = c ≫ H.map (Prod.mkHom mG.inv.op nG.hom)) :
    (uF.inv ≫ uG.hom) ≫ cG =
      cF ≫ H.map (Prod.mkHom (mG.inv ≫ mF.hom).op (nF.inv ≫ nG.hom)) := by
  apply (cancel_epi uF.hom).mp
  simp only [Iso.hom_inv_id_assoc, Category.assoc]
  rw [hG, ← Category.assoc, hF, Category.assoc]
  congr 1
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, ← op_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Bifunctoriality and inverse cancellation give the ambient transition tower. -/
lemma ambient_transition_tower
    {C : Type*} [Category C] (H : Cᵒᵖ × C ⥤ C)
    {M N MF NF MG NG MK NK : C}
    (mF : M ≅ MF) (nF : N ≅ NF) (mG : M ≅ MG) (nG : N ≅ NG)
    (mK : M ≅ MK) (nK : N ≅ NK) :
    H.map (Prod.mkHom (mG.inv ≫ mF.hom).op (nF.inv ≫ nG.hom)) ≫
        H.map (Prod.mkHom (mK.inv ≫ mG.hom).op (nG.inv ≫ nK.hom)) =
      H.map (Prod.mkHom (mK.inv ≫ mF.hom).op (nF.inv ≫ nK.hom)) := by
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, ← op_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

end AdicQbarRealization.AmbientHomEvaluation.CoherenceCalculus

end WeilConjectures
