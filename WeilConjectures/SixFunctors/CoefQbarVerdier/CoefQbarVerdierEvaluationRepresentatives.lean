/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierTensorInclusion

/-! Finite evaluation and its comparison on common-stage representatives. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096

universe u v w u₁ v₁ u₂ v₂

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarVerdier.tensorInclusion
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem evaluation_iso_formula {C : Type*} [Category C]
    (T : C × C ⥤ C) (d : Cᵒᵖ ⥤ C) (w : C)
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    (hn : ∀ {K M} (f : K ⟶ M),
      T.map (Prod.mkHom f (𝟙 _)) ≫ ev M =
        T.map (Prod.mkHom (𝟙 K) (d.map f.op)) ≫ ev K)
    {K K' P P' : C} (a : K ≅ K') (b : P ≅ P') (h : P' ⟶ d.obj (op K')) :
    T.map (Prod.mkHom (𝟙 K) (b.hom ≫ h ≫ d.map a.hom.op)) ≫ ev K =
      T.map (Prod.mkHom a.hom b.hom) ≫
        (T.map (Prod.mkHom (𝟙 K') h) ≫ ev K') := by
  calc
    _ = T.map (Prod.mkHom (𝟙 K) (b.hom ≫ h)) ≫
        (T.map (Prod.mkHom (𝟙 K) (d.map a.hom.op)) ≫ ev K) := by
          rw [← T.map_comp_assoc]
          congr 2
          simp
    _ = T.map (Prod.mkHom (𝟙 K) (b.hom ≫ h)) ≫
        (T.map (Prod.mkHom a.hom (𝟙 _)) ≫ ev K') := by rw [← hn a.hom]
    _ = _ := by
      simp only [← T.map_comp_assoc]
      congr 2
      simp

private theorem tensorEvaluationBijective {C : Type*} [Category C]
    (T : C × C ⥤ C) (K w d : C) (H : C ⥤ C)
    (adj : ((Functor.const C).obj K).prod' (𝟭 C) ⋙ T ⊣ H)
    (e : d ≅ H.obj w) (ev : T.obj (K, d) ⟶ w)
    (he : T.map (Prod.mkHom (𝟙 K) e.hom) ≫ adj.counit.app w = ev) (P : C) :
    Function.Bijective (fun h : P ⟶ d ↦ T.map (Prod.mkHom (𝟙 K) h) ≫ ev) := by
  let q := e.homToEquiv.trans ((adj.homEquiv P w).symm)
  have hq : (fun h : P ⟶ d ↦ T.map (Prod.mkHom (𝟙 K) h) ≫ ev) = q := by
    funext h
    change T.map (Prod.mkHom (𝟙 K) h) ≫ ev =
      T.map (Prod.mkHom (𝟙 K) (h ≫ e.hom)) ≫ adj.counit.app w
    rw [← he, ← Category.assoc, ← T.map_comp]
    congr 2
    simp
  rw [hq]
  exact q.bijective

private theorem isoToStage_compatible
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
    (P : S.PairCategory) {i j : I} (hi : P.stage ≤ i) (h : i ≤ j) :
    (S.ι j).map ((S.assoc hi h).hom.app P.obj) ≫
        (S.isoToStage P (hi.trans h)).inv =
      (S.transIso h).hom.app (P.toStage hi) ≫ (S.isoToStage P hi).inv := by
  rw [BilinearCoefficientDescent.isoToStage_inv_eq P hi h,
    StageSystem.transIso_hom_app]
  dsimp only [StageSystem.isoToStage]
  rw [StageSystem.ι_map_eq le_rfl, StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom j _ _)
  exact S.cocycle hi h (le_refl j) P.obj

private theorem tensorStagesCompatible
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
    (T : S.PairCategory × S.PairCategory ⥤ S.PairCategory)
    (U : ∀ i, C i × C i ⥤ C i)
    (t : ∀ {i j} (h : i ≤ j), U i ⋙ S.T h ≅ (S.T h).prod (S.T h) ⋙ U j)
    (e : ∀ i (K P : C i), (S.ι i).obj ((U i).obj (K, P)) ≅
      T.obj ((S.ι i).obj K, (S.ι i).obj P))
    (hn : ∀ i {K K' P P' : C i} (f : K ⟶ K') (g : P ⟶ P'),
      (S.ι i).map ((U i).map (Prod.mkHom f g)) ≫ (e i K' P').hom =
        (e i K P).hom ≫ T.map (Prod.mkHom ((S.ι i).map f) ((S.ι i).map g)))
    (hs : ∀ {i j} (h : i ≤ j) (K P : C i),
      (S.ι j).map ((t h).hom.app (K, P)) ≫
          (e j ((S.T h).obj K) ((S.T h).obj P)).hom ≫
          T.map (Prod.mkHom ((S.transIso h).hom.app K) ((S.transIso h).hom.app P)) =
        (S.transIso h).hom.app ((U i).obj (K, P)) ≫ (e i K P).hom)
    (K P : S.PairCategory) {i j : I} (hi : K.stage ≤ i) (hj : P.stage ≤ i) (h : i ≤ j) :
    (S.ι j).map ((t h).hom.app (K.toStage hi, P.toStage hj) ≫
        (U j).map (Prod.mkHom ((S.assoc hi h).hom.app K.obj)
          ((S.assoc hj h).hom.app P.obj))) ≫
      (e j (K.toStage (hi.trans h)) (P.toStage (hj.trans h))).hom ≫
      T.map (Prod.mkHom (S.isoToStage K (hi.trans h)).inv
        (S.isoToStage P (hj.trans h)).inv) =
    (S.transIso h).hom.app ((U i).obj (K.toStage hi, P.toStage hj)) ≫
      (e i (K.toStage hi) (P.toStage hj)).hom ≫
      T.map (Prod.mkHom (S.isoToStage K hi).inv (S.isoToStage P hj).inv) := by
  rw [(S.ι j).map_comp, Category.assoc,
    reassoc_of% (hn j ((S.assoc hi h).hom.app K.obj) ((S.assoc hj h).hom.app P.obj))]
  rw [← T.map_comp]
  simp only [prod_comp]
  rw [isoToStage_compatible S K hi h, isoToStage_compatible S P hj h]
  rw [show Prod.mkHom
      ((S.transIso h).hom.app (K.toStage hi) ≫ (S.isoToStage K hi).inv)
      ((S.transIso h).hom.app (P.toStage hj) ≫ (S.isoToStage P hj).inv) =
    Prod.mkHom ((S.transIso h).hom.app (K.toStage hi))
      ((S.transIso h).hom.app (P.toStage hj)) ≫
    Prod.mkHom (S.isoToStage K hi).inv (S.isoToStage P hj).inv by rfl]
  rw [T.map_comp, reassoc_of% (hs h (K.toStage hi) (P.toStage hj))]

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageSystem stageSystem_existsUnique)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedTensor sfRationalScalarExtension rationalTensorScalarComparison
attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage Duality
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.uniformProd Duality
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory

private theorem tensor_inclusion_natural (E : Index l Ω) {K K' P P' : Stage l Ω X E}
    (f : K ⟶ K') (g : P ⟶ P') :
    (inclusion E).map
        ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map (Prod.mkHom f g)) ≫
        (tensorInclusion D l hl Ω X E K' P').hom =
      (tensorInclusion D l hl Ω X E K P).hom ≫
        (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom ((inclusion E).map f) ((inclusion E).map g))  := by
  exact (tensorInclusion_coherent D l hl Ω X).1 E f g

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
        (tensorInclusion D l hl Ω X E K P).hom  := by
  exact (tensorInclusion_coherent D l hl Ω X).2 h K P

private theorem finiteEvaluation_global (B : Duality D l hl Ω X)
    (E : Index l Ω) (K P : Stage l Ω X E)
    (f : P ⟶ (B.finite.datum E).dual.obj (op K)) :
    (CoefQbarTensor D l hl Ω X).map
      (Prod.mkHom (𝟙 ((inclusion E).obj K))
        ((inclusion E).map f ≫ (B.comparison E).hom.app (op K))) ≫
      B.evaluation ((inclusion E).obj K) =
    (tensorInclusion D l hl Ω X E K P).inv ≫
      (inclusion E).map
        ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map
          (Prod.mkHom (𝟙 K) f) ≫ (B.finite.datum E).evaluation K) ≫
        (B.omegaComparison E).hom := by
  have he := B.property.2.2.2.2.2.2.2.2.2.1
  apply (cancel_epi (tensorInclusion D l hl Ω X E K P).hom).mp
  have hn := tensor_inclusion_natural D l hl Ω X E (𝟙 K) f
  rw [(inclusion E).map_id] at hn
  simp only [Iso.hom_inv_id_assoc]
  calc
    _ = (tensorInclusion D l hl Ω X E K P).hom ≫
        (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom (𝟙 ((inclusion E).obj K)) ((inclusion E).map f)) ≫
        (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom (𝟙 ((inclusion E).obj K)) ((B.comparison E).hom.app (op K))) ≫
        B.evaluation ((inclusion E).obj K) := by
      rw [← (CoefQbarTensor D l hl Ω X).map_comp_assoc]
      congr 3
      simp
    _ = _ := by
      rw [← reassoc_of% hn, he E K]
      simp only [Functor.map_comp, Category.assoc]

private theorem tensorObject_compatible
    (K P : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    {E L : Index l Ω} (hi : K.stage ≤ E) (hj : P.stage ≤ E) (h : E ≤ L) :
    let := RationalVerdier.units D l hl X
    (inclusion L).map
      ((rationalTensorStageComparison l Ω X h).hom.app (K.toStage hi, P.toStage hj) ≫
        (rationalDerivedTensor l (Coefficient.{u} l Ω L) X).map
          (Prod.mkHom (((stageSystem l Ω X).assoc hi h).hom.app K.obj)
            (((stageSystem l Ω X).assoc hj h).hom.app P.obj))) ≫
      (tensorInclusion D l hl Ω X L (K.toStage (hi.trans h))
        (P.toStage (hj.trans h))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom ((stageSystem l Ω X).isoToStage K (hi.trans h)).inv
          ((stageSystem l Ω X).isoToStage P (hj.trans h)).inv) =
    ((stageSystem l Ω X).transIso h).hom.app
      ((rationalDerivedTensor l (Coefficient.{u} l Ω E) X).obj
        (K.toStage hi, P.toStage hj)) ≫
      (tensorInclusion D l hl Ω X E (K.toStage hi) (P.toStage hj)).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom ((stageSystem l Ω X).isoToStage K hi).inv
          ((stageSystem l Ω X).isoToStage P hj).inv) := by
  let := RationalVerdier.units D l hl X
  exact tensorStagesCompatible (C := Stage l Ω X) (stageSystem l Ω X)
    (CoefQbarTensor D l hl Ω X)
    (fun i ↦ rationalDerivedTensor l (Coefficient.{u} l Ω i) X)
    (fun {_ _} h ↦ rationalTensorStageComparison l Ω X h)
    (tensorInclusion D l hl Ω X)
    (fun i {_ _ _ _} f g ↦ tensor_inclusion_natural D l hl Ω X i f g)
    (fun {_ _} h K P ↦ tensor_inclusion_scalar D l hl Ω X h K P) K P hi hj h

/-- Finite evaluation is bijective and agrees with global evaluation on representatives.
Source: blueprint thm-coef-qbar-verdier, tensor-Hom and evaluation descent in step 5.
(blueprint: lem-coef-qbar-evaluation-representatives).
Proof: conjugate the finite tensor-Hom adjunction's Hom equivalence by its
prescribed duality isomorphism; the counit normalization gives the stated finite
transpose. For the global formula, move the endpoint isomorphisms through tensor
and use evaluation naturality in its first variable. Tensor-inclusion naturality
and the prescribed finite evaluation square identify the result with finite
evaluation. Finally tensor-inclusion naturality, its scalar square, and the
composition identity for isoToStage give the representative tensor square.
None of these steps needs scalar extension to be faithful. -/
theorem finite_evaluation_representatives (B : Duality D l hl Ω X) :
    (∀ (E : Index l Ω) (K P : Stage l Ω X E),
      Function.Bijective (fun f : P ⟶ (B.finite.datum E).dual.obj (op K) ↦
        (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map
          (Prod.mkHom (𝟙 K) f) ≫ (B.finite.datum E).evaluation K)) ∧
    (∀ (K P : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (E : Index l Ω) (hK : K.stage ≤ E) (hP : P.stage ≤ E)
      (f : P.toStage hP ⟶ (B.finite.datum E).dual.obj (op (K.toStage hK))),
      (CoefQbarTensor D l hl Ω X).map (Prod.mkHom (𝟙 K)
        (((stageSystem l Ω X).isoToStage P hP).hom ≫ (inclusion E).map f ≫
          (B.comparison E).hom.app (op (K.toStage hK)) ≫
            B.duality.dual.map (((stageSystem l Ω X).isoToStage K hK).hom).op)) ≫
        B.evaluation K =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom ((stageSystem l Ω X).isoToStage K hK).hom
          ((stageSystem l Ω X).isoToStage P hP).hom) ≫
        (tensorInclusion D l hl Ω X E (K.toStage hK) (P.toStage hP)).inv ≫
          (inclusion E).map
            ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map
              (Prod.mkHom (𝟙 (K.toStage hK)) f) ≫
                (B.finite.datum E).evaluation (K.toStage hK)) ≫
            (B.omegaComparison E).hom) ∧
    (∀ (K P : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    {E L : Index l Ω} (hi : K.stage ≤ E) (hj : P.stage ≤ E) (h : E ≤ L),
    let := RationalVerdier.units D l hl X
    (inclusion L).map
      ((rationalTensorStageComparison l Ω X h).hom.app (K.toStage hi, P.toStage hj) ≫
        (rationalDerivedTensor l (Coefficient.{u} l Ω L) X).map
          (Prod.mkHom (((stageSystem l Ω X).assoc hi h).hom.app K.obj)
            (((stageSystem l Ω X).assoc hj h).hom.app P.obj))) ≫
      (tensorInclusion D l hl Ω X L (K.toStage (hi.trans h))
        (P.toStage (hj.trans h))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom ((stageSystem l Ω X).isoToStage K (hi.trans h)).inv
          ((stageSystem l Ω X).isoToStage P (hj.trans h)).inv) =
    ((stageSystem l Ω X).transIso h).hom.app
      ((rationalDerivedTensor l (Coefficient.{u} l Ω E) X).obj
        (K.toStage hi, P.toStage hj)) ≫
      (tensorInclusion D l hl Ω X E (K.toStage hi) (P.toStage hj)).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom ((stageSystem l Ω X).isoToStage K hi).inv
          ((stageSystem l Ω X).isoToStage P hj).inv)) := by
  let := RationalVerdier.units D l hl X
  refine ⟨?_, ?_, ?_⟩
  · intro E K P
    exact tensorEvaluationBijective (C := Stage l Ω X E)
      (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)) K
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (B.finite.omega E).omega) ((B.finite.datum E).dual.obj (op K))
      (RationalOperations.homRight l (Coefficient.{u} l Ω E) X (B.finite.hom E).permitted K)
      ((B.finite.hom E).adjunction K) ((B.finite.hom E).duality.app (op K))
      ((B.finite.datum E).evaluation K) ((B.finite.hom E).evaluation K) P
  · intro K P E hK hP f
    have hn := B.property.2.2.2.2.2.2.2.2.2.2.1
    have he := evaluation_iso_formula (CoefQbarTensor D l hl Ω X) B.duality.dual B.omega
      B.evaluation (fun {_ _} f ↦ hn _ _ f)
      ((stageSystem l Ω X).isoToStage K hK) ((stageSystem l Ω X).isoToStage P hP)
      ((inclusion E).map f ≫ (B.comparison E).hom.app (op (K.toStage hK)))
    rw [finiteEvaluation_global D l hl Ω X B E _ _ f] at he
    simpa only [Category.assoc] using he
  · intro K P E L hi hj h
    exact tensorObject_compatible D l hl Ω X K P hi hj h

end WeilConjectures.CoefQbarVerdier
