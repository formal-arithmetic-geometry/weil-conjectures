/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
import WeilConjectures.SixFunctors.Normalized.NormalizedRationalEvaluationNaturality
import WeilConjectures.SmoothPurity.CommonStageInternalHomDescent.CommonStageInternalHomDescent

/-! # Naturality of normalized common-stage evaluation

Source: blueprint latest, lem-fix-weil-operations.proof.md, evaluation paragraph;
derived-automorphism Hom evaluation, common-stage descent, steps 15--16
(blueprint: lem-pod-normalized-common-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v a b
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  commonStageDerivedTensor commonStageDerivedInternalHom commonStageTensorComparison
  commonStageHomComparison podCommonClosed podRationalClosed
  rationalDerivedTensor rationalDerivedInternalHom ScalarLocalization.composition
  StageSystem.PairCategory.mkHom

private theorem partial_uncurry
    {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (L : C) (P : J.FullSubcategory) (f : L ⟶ H.obj P) :
    (S.transpose L P).symm f = T.map (Prod.mkHom f (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose L P).injective
  rw [S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

private theorem tensor_exchange
    {C : Type a} [Category.{b} C] {D : Type*} [Category D] (T : C × C ⥤ D)
    {A B M N : C} (f : A ⟶ B) (g : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 A) g) ≫ T.map (Prod.mkHom f (𝟙 N)) =
      T.map (Prod.mkHom f (𝟙 M)) ≫ T.map (Prod.mkHom (𝟙 B) g) := by
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  ext <;> simp

private theorem tensor_cancel
    {C : Type a} [Category.{b} C] {D : Type*} [Category D] (T : C × C ⥤ D)
    {A B C' E M : C} (f : A ⟶ B) (g : B ⟶ C') (e : E ≅ C') :
    T.map (Prod.mkHom (f ≫ g ≫ e.inv) (𝟙 M)) ≫
        T.map (Prod.mkHom e.hom (𝟙 M)) =
      T.map (Prod.mkHom f (𝟙 M)) ≫ T.map (Prod.mkHom g (𝟙 M)) := by
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  ext <;> simp

private theorem tensor_conjugation_naturality
    {C : Type a} [Category.{b} C] (T : C × C ⥤ C)
    {X Y H K A A' B B' U V V' : C}
    (cP : X ≅ H) (cQ : Y ≅ K)
    (tU : U ≅ T.obj (X, A')) (tP : V ≅ T.obj (X, A)) (tQ : V' ≅ T.obj (Y, A'))
    (f : H ⟶ K) (a : A' ⟶ A) (b : B ⟶ B')
    (eP : T.obj (H, A) ⟶ B) (eQ : T.obj (K, A') ⟶ B')
    (hn : T.map (Prod.mkHom f (𝟙 A')) ≫ eQ =
      T.map (Prod.mkHom (𝟙 H) a) ≫ eP ≫ b) :
    (tU.hom ≫ T.map (Prod.mkHom (cP.hom ≫ f ≫ cQ.inv) (𝟙 A')) ≫ tQ.inv) ≫
        tQ.hom ≫ T.map (Prod.mkHom cQ.hom (𝟙 A')) ≫ eQ =
      (tU.hom ≫ T.map (Prod.mkHom (𝟙 X) a) ≫ tP.inv) ≫
        (tP.hom ≫ T.map (Prod.mkHom cP.hom (𝟙 A)) ≫ eP) ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have he : T.map (Prod.mkHom (cP.hom ≫ f ≫ cQ.inv) (𝟙 A')) ≫
      T.map (Prod.mkHom cQ.hom (𝟙 A')) ≫ eQ =
      T.map (Prod.mkHom (𝟙 X) a) ≫ T.map (Prod.mkHom cP.hom (𝟙 A)) ≫ eP ≫ b := by
    calc
      _ = (T.map (Prod.mkHom cP.hom (𝟙 A')) ≫
          T.map (Prod.mkHom f (𝟙 A'))) ≫ eQ := by
        rw [← Category.assoc, tensor_cancel]
      _ = T.map (Prod.mkHom cP.hom (𝟙 A')) ≫
          (T.map (Prod.mkHom (𝟙 H) a) ≫ eP ≫ b) := by
        rw [Category.assoc, hn]
      _ = _ := by
        rw [← Category.assoc _ _ (eP ≫ b), ← tensor_exchange]
        simp only [Category.assoc]
  exact congrArg (fun k ↦ tU.hom ≫ k) he

set_option linter.auxLemma false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomPairAtStage
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
  GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  ObjectProperty.FullSubcategory.category
attribute [local implicit_reducible] catToReflQuiver
attribute [local irreducible] ScalarLocalization.category
attribute [local instance 2000] GeneralAlgebraicallyClosedCoefficients.pairCategory
  GeneralAlgebraicallyClosedCoefficients.preadditive

section EvaluationNormalization
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem hom_obj_eq
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    (commonStageDerivedInternalHom l Ω W).obj P = commonStageHomObject l Ω W P := by
  unfold commonStageDerivedInternalHom
  exact (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.1 P

private theorem tensor_obj_eq
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    (commonStageDerivedTensor l Ω W).obj (M, N) = commonStageTensorObject l Ω W M N := by
  unfold commonStageDerivedTensor
  exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 M N

omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem identity_heq
    (M A : generalAlgebraicallyClosedConstructibleCategory l Ω W) (h : M = A)
    (F : Index l Ω) (hA : A.stage ≤ F) :
    HEq (𝟙 M) (ofHom A A F hA hA (𝟙 _)) := by
  cases h
  exact heq_of_eq (StageSystem.PairCategory.id_eq_mkHom M hA)

private theorem tensor_map_normalization
    (M M' N N' A A' B B' : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (hM : M = A) (hM' : M' = A') (hN : N = B) (hN' : N' = B')
    (F : Index l Ω)
    (h : (commonStageTensorObject l Ω W A B).stage ≤ F)
    (h' : (commonStageTensorObject l Ω W A' B').stage ≤ F)
    (a : A.toStage
      (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h) ⟶
      A'.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).1.trans h'))
    (b : B.toStage
      (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h) ⟶
      B'.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).2.trans h'))
    (f : M ⟶ M') (g : N ⟶ N')
    (hf : HEq f (ofHom A A' F
      (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h)
      (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).1.trans h') a))
    (hg : HEq g (ofHom B B' F
      (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)
      (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage B'.stage).2.trans h') b)) :
    HEq ((commonStageDerivedTensor l Ω W).map (Prod.mkHom f g))
      (ofHom (commonStageTensorObject l Ω W A B) (commonStageTensorObject l Ω W A' B')
        F h h' ((commonStageTensorComparison l Ω W A B F h).hom ≫
          (rationalDerivedTensor l (Coefficient.{u} l Ω F) W).map (Prod.mkHom a b) ≫
          (commonStageTensorComparison l Ω W A' B' F h').inv)) := by
  cases hM
  cases hM'
  cases hN
  cases hN'
  rw [eq_of_heq hf, eq_of_heq hg]
  unfold commonStageDerivedTensor
  exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.2
    M N M' N' F h h' a b

private theorem evaluation_transport
    {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (P : J.FullSubcategory) (B : C) (h : H.obj P = B) :
    HEq (S.evaluation P) ((S.transpose B P).symm (eqToHom h.symm)) := by
  subst B
  rfl

private theorem identity_transport {C : Type a} [Category.{b} C]
    {A B : C} (h : A = B) : HEq (eqToHom h.symm) (𝟙 A) := by
  subst B
  rfl

private theorem evaluation_normalization
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (F : Index l Ω) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W
      (commonStageHomObject l Ω W P) P.obj.1.unop).stage ≤ F)
    (hN : P.obj.2.stage ≤ F) :
    HEq ((podCommonClosed l Ω W).evaluation P)
      (ofHom (commonStageTensorObject l Ω W
        (commonStageHomObject l Ω W P) P.obj.1.unop) P.obj.2 F hT hN
        ((commonStageTensorComparison l Ω W
          (commonStageHomObject l Ω W P) P.obj.1.unop F hT).hom ≫
          (rationalDerivedTensor l (Coefficient.{u} l Ω F) W).map
            (Prod.mkHom (commonStageHomComparison l Ω W P F hP).hom (𝟙 _)) ≫
          (podRationalClosed l (Coefficient.{u} l Ω F) W).evaluation
            (commonStageHomPairAtStage l Ω W P F hP))) := by
  have hX := hom_obj_eq l Ω W P
  have hn : PodCommonTransposeNormalization l Ω W (podCommonClosed l Ω W) := by
    delta podCommonClosed
    exact (podCommonClosed_existsUnique l Ω W).exists.choose_spec
  have hi := (identity_transport hX).trans
    (identity_heq l Ω W _ _ hX F hP)
  have h := (evaluation_transport (podCommonClosed l Ω W) P _ hX).trans
    (hn (commonStageHomObject l Ω W P) P F hP hP hT hN (𝟙 _) (eqToHom hX.symm) hi)
  rw [Category.id_comp] at h
  have he := partial_uncurry (podRationalClosed l (Coefficient.{u} l Ω F) W)
    ((commonStageHomObject l Ω W P).toStage hP)
    (commonStageHomPairAtStage l Ω W P F hP)
    (commonStageHomComparison l Ω W P F hP).hom
  rw [he] at h
  exact h

end EvaluationNormalization

/-- The Hom-first common-stage evaluation is natural in both internal-Hom entries.
No separatedness or finite-type hypothesis is needed for this coefficient identity.
Source: blueprint latest, lem-fix-weil-operations.proof.md, evaluation paragraph;
lem-pod-derived-automorphism-hom-evaluation, steps 15--16.

Proof: choose one finite coefficient field representing both permitted pairs and
both components of the pair arrow. Enlarge it to contain the tensor and internal-Hom
object stages and all the finite comparisons. The prescribed common-stage tensor
and Hom functor formulas express their maps by conjugating the rational maps at
this field. The normalization of podCommonClosed, specialized to the identity
transpose, expresses each evaluation by the rational evaluation, conjugated by the
same tensor and Hom comparisons. Substitute these expressions into both sides.
The intervening Hom and tensor comparisons cancel; the remaining equality is
normalizedRationalEvaluation_naturality at that finite field. The scalar comparison
preserves evaluation and obeys the tower cocycle, so a further common enlargement
preserves this equality. Equal representatives define equal classes; therefore the
two common-stage composites are equal, for arbitrary morphisms of the actual
category. Identity and zero pair arrows give respectively the identity and zero
naturality equations, and no injectivity of a scalar transition is used.
(blueprint: lem-pod-normalized-common-evaluation-naturality). -/
theorem normalizedCommonEvaluation_naturality
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P P' : (commonStageHomPairs l Ω W).FullSubcategory) (g : P ⟶ P') :
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom ((commonStageDerivedInternalHom l Ω W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podCommonClosed l Ω W).evaluation P' =
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom l Ω W).obj P)) g.hom.1.unop) ≫
      (podCommonClosed l Ω W).evaluation P ≫ g.hom.2 := by
  let HP := commonStageHomObject l Ω W P
  let HQ := commonStageHomObject l Ω W P'
  let TP := commonStageTensorObject l Ω W HP P.obj.1.unop
  let TQ := commonStageTensorObject l Ω W HQ P'.obj.1.unop
  let TU := commonStageTensorObject l Ω W HP P'.obj.1.unop
  obtain ⟨N, hTP, hTQ⟩ := exists_ge_ge TP.stage TQ.stage
  obtain ⟨N', hN, hTU⟩ := exists_ge_ge N TU.stage
  obtain ⟨F, hNF, hP, hQ, a, b, hg⟩ :=
    CommonStageInternalHomDescent.homRepresentative_exists l Ω W P P' g N'
  let hTPF := hTP.trans (hN.trans hNF)
  let hTQF := hTQ.trans (hN.trans hNF)
  let hTUF := hTU.trans hNF
  let PR := commonStageHomPairAtStage l Ω W P F hP
  let QR := commonStageHomPairAtStage l Ω W P' F hQ
  let TR := rationalDerivedTensor l (Coefficient.{u} l Ω F) W
  let HR := rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W
  let SR := podRationalClosed l (Coefficient.{u} l Ω F) W
  let gR : PR ⟶ QR := ObjectProperty.homMk (Prod.mkHom a.op b)
  let cP := commonStageHomComparison l Ω W P F hP
  let cQ := commonStageHomComparison l Ω W P' F hQ
  let tP := commonStageTensorComparison l Ω W HP P.obj.1.unop F hTPF
  let tQ := commonStageTensorComparison l Ω W HQ P'.obj.1.unop F hTQF
  let tU := commonStageTensorComparison l Ω W HP P'.obj.1.unop F hTUF
  have hHP := hom_obj_eq l Ω W P
  have hHQ := hom_obj_eq l Ω W P'
  have hmap : HEq ((commonStageDerivedInternalHom l Ω W).map g)
      (ofHom HP HQ F hP hQ (cP.hom ≫ HR.map gR ≫ cQ.inv)) := by
    rw [hg]
    unfold commonStageDerivedInternalHom
    exact (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.2
      P P' F hP hQ a b
  have hleft := tensor_map_normalization l Ω W
    ((commonStageDerivedInternalHom l Ω W).obj P)
    ((commonStageDerivedInternalHom l Ω W).obj P') P'.obj.1.unop P'.obj.1.unop
    HP HQ P'.obj.1.unop P'.obj.1.unop hHP hHQ rfl rfl F hTUF hTQF
    (cP.hom ≫ HR.map gR ≫ cQ.inv) (𝟙 _)
    ((commonStageDerivedInternalHom l Ω W).map g) (𝟙 _) hmap
    (identity_heq l Ω W _ _ rfl F _)
  have hidHP := identity_heq l Ω W
    ((commonStageDerivedInternalHom l Ω W).obj P) HP hHP F hP
  have ha : HEq g.hom.1.unop
      (ofHom P'.obj.1.unop P.obj.1.unop F
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P'.obj.1.unop.stage P'.obj.2.stage).1.trans hQ)
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans hP) a) := by
    rw [hg]
    rfl
  have hb : g.hom.2 = ofHom P.obj.2 P'.obj.2 F
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans hP)
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P'.obj.1.unop.stage P'.obj.2.stage).2.trans hQ) b := by
    rw [hg]
    rfl
  have hright := tensor_map_normalization l Ω W
    ((commonStageDerivedInternalHom l Ω W).obj P)
    ((commonStageDerivedInternalHom l Ω W).obj P) P'.obj.1.unop P.obj.1.unop
    HP HP P'.obj.1.unop P.obj.1.unop hHP hHP rfl rfl F hTUF hTPF
    (𝟙 _) a (𝟙 _) g.hom.1.unop hidHP ha
  have hevP := evaluation_normalization l Ω W P F hP hTPF
    (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans hP)
  have hevQ := evaluation_normalization l Ω W P' F hQ hTQF
    (((Padic.finiteCoefficientFields_properties l Ω).1
      P'.obj.1.unop.stage P'.obj.2.stage).2.trans hQ)
  have hobj (A : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
      (commonStageDerivedTensor l Ω W).obj
          ((commonStageDerivedInternalHom l Ω W).obj P, A) =
        commonStageTensorObject l Ω W HP A := by
    rw [hHP]
    exact tensor_obj_eq l Ω W HP A
  have hobjQ : (commonStageDerivedTensor l Ω W).obj
      ((commonStageDerivedInternalHom l Ω W).obj P', P'.obj.1.unop) = TQ := by
    rw [hHQ]
    exact tensor_obj_eq l Ω W HQ P'.obj.1.unop
  have lhs := heq_comp (hobj P'.obj.1.unop) hobjQ rfl hleft hevQ
  have rhs₀ := heq_comp (hobj P.obj.1.unop) rfl rfl hevP (heq_of_eq hb)
  have rhs := heq_comp (hobj P'.obj.1.unop) (hobj P.obj.1.unop) rfl hright rhs₀
  apply eq_of_heq
  refine lhs.trans ((heq_of_eq ?_).trans rhs.symm)
  simp only [StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (ofHom TU P'.obj.2 F hTUF
    (((Padic.finiteCoefficientFields_properties l Ω).1
      P'.obj.1.unop.stage P'.obj.2.stage).2.trans hQ))
  change (tU.hom ≫ TR.map (Prod.mkHom (cP.hom ≫ HR.map gR ≫ cQ.inv) (𝟙 _)) ≫
      tQ.inv) ≫ tQ.hom ≫ TR.map (Prod.mkHom cQ.hom (𝟙 _)) ≫ SR.evaluation QR =
    (tU.hom ≫ TR.map (Prod.mkHom (𝟙 _) a) ≫ tP.inv) ≫
      (tP.hom ≫ TR.map (Prod.mkHom cP.hom (𝟙 _)) ≫ SR.evaluation PR) ≫ b
  exact tensor_conjugation_naturality TR cP cQ tU tP tQ (HR.map gR) a b
    (SR.evaluation PR) (SR.evaluation QR)
    (normalizedRationalEvaluation_naturality l (Coefficient.{u} l Ω F) W PR QR gR)

end WeilConjectures
