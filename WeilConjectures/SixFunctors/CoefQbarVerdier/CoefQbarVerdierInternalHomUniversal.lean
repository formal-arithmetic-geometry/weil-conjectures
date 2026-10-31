/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierEvaluationRepresentatives
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierDualInclusion
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFiniteEvaluationScalar

/-! Universal property transport for the common-stage internal Hom.

Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
-/

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
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

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

section StageHom
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
  {i₀ : I} (A B : ∀ i, i₀ ≤ i → C i) {A₀ B₀ : S.PairCategory}
  (a : ∀ i h, (S.ι i).obj (A i h) ≅ A₀)
  (b : ∀ i h, (S.ι i).obj (B i h) ≅ B₀)

private def stageHomLift (i : I) (h : i₀ ≤ i) (f : A i h ⟶ B i h) : A₀ ⟶ B₀ :=
  (a i h).inv ≫ (S.ι i).map f ≫ (b i h).hom

private theorem stageHomLift_normal (i j : I) (hi : i₀ ≤ i) (h : i ≤ j)
    (sa : (S.T h).obj (A i hi) ≅ A j (hi.trans h))
    (sb : (S.T h).obj (B i hi) ≅ B j (hi.trans h))
    (ha : (S.ι j).map sa.hom ≫ (a j (hi.trans h)).hom =
      (S.transIso h).hom.app (A i hi) ≫ (a i hi).hom)
    (hb : (S.ι j).map sb.hom ≫ (b j (hi.trans h)).hom =
      (S.transIso h).hom.app (B i hi) ≫ (b i hi).hom)
    (f : (S.T h).obj (A i hi) ⟶ (S.T h).obj (B i hi)) :
    stageHomLift S A B a b j (hi.trans h) (sa.inv ≫ f ≫ sb.hom) =
      (a i hi).inv ≫ (S.transIso h).inv.app (A i hi) ≫ (S.ι j).map f ≫
        (S.transIso h).hom.app (B i hi) ≫ (b i hi).hom := by
  have hea : (S.ι j).mapIso sa ≪≫ a j (hi.trans h) =
      (S.transIso h).app (A i hi) ≪≫ a i hi := Iso.ext ha
  have hea' := congrArg Iso.inv hea
  dsimp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app] at hea'
  dsimp only [stageHomLift]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (a j _).inv, hea']
  simp only [Category.assoc, hb]

private theorem stageHomLift_transport (i j : I) (hi : i₀ ≤ i) (h : i ≤ j)
    (sa : (S.T h).obj (A i hi) ≅ A j (hi.trans h))
    (sb : (S.T h).obj (B i hi) ≅ B j (hi.trans h))
    (ha : (S.ι j).map sa.hom ≫ (a j (hi.trans h)).hom =
      (S.transIso h).hom.app (A i hi) ≫ (a i hi).hom)
    (hb : (S.ι j).map sb.hom ≫ (b j (hi.trans h)).hom =
      (S.transIso h).hom.app (B i hi) ≫ (b i hi).hom)
    (f : A i hi ⟶ B i hi) :
    stageHomLift S A B a b j (hi.trans h) (sa.inv ≫ (S.T h).map f ≫ sb.hom) =
      stageHomLift S A B a b i hi f := by
  rw [stageHomLift_normal S A B a b i j hi h sa sb ha hb]
  have hn : (S.transIso h).inv.app (A i hi) ≫ (S.ι j).map ((S.T h).map f) =
      (S.ι i).map f ≫ (S.transIso h).inv.app (B i hi) :=
    ((S.transIso h).inv.naturality f).symm
  simp only [stageHomLift]
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem stageHomLift_surjective
    (sa : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j),
      (S.T h).obj (A i hi) ≅ A j (hi.trans h))
    (sb : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j),
      (S.T h).obj (B i hi) ≅ B j (hi.trans h))
    (ha : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j), (S.ι j).map (sa i j hi h).hom ≫ (a j (hi.trans h)).hom =
      (S.transIso h).hom.app (A i hi) ≫ (a i hi).hom)
    (hb : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j), (S.ι j).map (sb i j hi h).hom ≫ (b j (hi.trans h)).hom =
      (S.transIso h).hom.app (B i hi) ≫ (b i hi).hom)
    (f : A₀ ⟶ B₀) :
    ∃ (i : I) (hi : i₀ ≤ i) (g : A i hi ⟶ B i hi), stageHomLift S A B a b i hi g = f := by
  let r := (a i₀ le_rfl).hom ≫ f ≫ (b i₀ le_rfl).inv
  obtain ⟨j, hj, hA, hB, u, hu⟩ :=
    StageSystem.PairCategory.exists_le_mkHom_eq r i₀
  refine ⟨j, hj, (sa i₀ j le_rfl hj).inv ≫ u ≫ (sb i₀ j le_rfl hj).hom, ?_⟩
  rw [stageHomLift_normal S A B a b i₀ j le_rfl hj _ _ (ha _ _ _ _) (hb _ _ _ _)]
  have hr : r = (S.transIso hj).inv.app (A i₀ le_rfl) ≫ (S.ι j).map u ≫
      (S.transIso hj).hom.app (B i₀ le_rfl) :=
    hu.trans (StageSystem.mkHom_eq_isoToStage hA hB u)
  rw [← reassoc_of% hr]
  simp only [r, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem stageHomLift_eq_eventually (i : I) (hi : i₀ ≤ i)
    (f g : A i hi ⟶ B i hi)
    (he : stageHomLift S A B a b i hi f = stageHomLift S A B a b i hi g) :
    ∃ (j : I) (h : i ≤ j), (S.T h).map f = (S.T h).map g := by
  have he' : (S.ι i).map f = (S.ι i).map g := by
    simpa only [stageHomLift, cancel_epi, cancel_mono] using he
  exact (S.ι_map_eq_ι_map_iff f g).mp he'
end StageHom

private structure HomStages
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    (S : StageSystem C) (i₀ : I) (A₀ B₀ : S.PairCategory) where
  source : ∀ i, i₀ ≤ i → C i
  target : ∀ i, i₀ ≤ i → C i
  sourceIso : ∀ i h, (S.ι i).obj (source i h) ≅ A₀
  targetIso : ∀ i h, (S.ι i).obj (target i h) ≅ B₀
  sourceScalar : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j),
    (S.T h).obj (source i hi) ≅ source j (hi.trans h)
  targetScalar : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j),
    (S.T h).obj (target i hi) ≅ target j (hi.trans h)
  source_compatible : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j),
    (S.ι j).map (sourceScalar i j hi h).hom ≫ (sourceIso j (hi.trans h)).hom =
      (S.transIso h).hom.app (source i hi) ≫ (sourceIso i hi).hom
  target_compatible : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j),
    (S.ι j).map (targetScalar i j hi h).hom ≫ (targetIso j (hi.trans h)).hom =
      (S.transIso h).hom.app (target i hi) ≫ (targetIso i hi).hom

private abbrev HomStages.lift
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {S : StageSystem C} {i₀ : I} {A₀ B₀ : S.PairCategory}
    (H : HomStages S i₀ A₀ B₀) :=
  stageHomLift S H.source H.target H.sourceIso H.targetIso

private abbrev HomStages.transport
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {S : StageSystem C} {i₀ : I} {A₀ B₀ : S.PairCategory}
    (H : HomStages S i₀ A₀ B₀) (i j : I) (hi : i₀ ≤ i) (h : i ≤ j)
    (f : H.source i hi ⟶ H.target i hi) :=
  (H.sourceScalar i j hi h).inv ≫ (S.T h).map f ≫ (H.targetScalar i j hi h).hom

private theorem HomStages.refine
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {S : StageSystem C} {i₀ : I} {A₀ B₀ : S.PairCategory}
    (H : HomStages S i₀ A₀ B₀) (i j : I) (hi : i₀ ≤ i) (h : i ≤ j)
    (f : H.source i hi ⟶ H.target i hi) :
    H.lift j (hi.trans h) (H.transport i j hi h f) = H.lift i hi f :=
  stageHomLift_transport S H.source H.target H.sourceIso H.targetIso i j hi h
    (H.sourceScalar i j hi h) (H.targetScalar i j hi h)
    (H.source_compatible i j hi h) (H.target_compatible i j hi h) f

private theorem HomStages.surjective
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {S : StageSystem C} {i₀ : I} {A₀ B₀ : S.PairCategory}
    (H : HomStages S i₀ A₀ B₀) (f : A₀ ⟶ B₀) :
    ∃ (i : I) (hi : i₀ ≤ i) (g : H.source i hi ⟶ H.target i hi), H.lift i hi g = f :=
  stageHomLift_surjective S H.source H.target H.sourceIso H.targetIso
    H.sourceScalar H.targetScalar H.source_compatible H.target_compatible f

private theorem stageEvaluationBijective
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {S : StageSystem C} {i₀ : I} {A₀ B₀ C₀ D₀ : S.PairCategory}
    (H : HomStages S i₀ A₀ B₀) (J : HomStages S i₀ C₀ D₀)
    (φ : ∀ i hi, (H.source i hi ⟶ H.target i hi) → (J.source i hi ⟶ J.target i hi))
    (hφ : ∀ i hi, Function.Bijective (φ i hi))
    (hscalar : ∀ i j (hi : i₀ ≤ i) (h : i ≤ j) f,
      φ j (hi.trans h) (H.transport i j hi h f) = J.transport i j hi h (φ i hi f))
    (Φ : (A₀ ⟶ B₀) → (C₀ ⟶ D₀))
    (hΦ : ∀ i hi f, Φ (H.lift i hi f) = J.lift i hi (φ i hi f)) :
    Function.Bijective Φ := by
  constructor
  · intro f g he
    obtain ⟨i, hi, u, rfl⟩ := H.surjective f
    obtain ⟨j, hj, v, rfl⟩ := H.surjective g
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let u' := H.transport i k hi hik u
    let v' := H.transport j k hj hjk v
    have he' : J.lift k (hi.trans hik) (φ k (hi.trans hik) u') =
        J.lift k (hi.trans hik) (φ k (hi.trans hik) v') := by
      rw [← hΦ, ← hΦ, H.refine, H.refine]
      exact he
    obtain ⟨m, hkm, hm⟩ := stageHomLift_eq_eventually S
      J.source J.target J.sourceIso J.targetIso k (hi.trans hik) _ _ he'
    have hf : H.transport k m (hi.trans hik) hkm u' =
        H.transport k m (hi.trans hik) hkm v' := by
      apply (hφ m _).injective
      rw [hscalar k m (hi.trans hik) hkm u', hscalar k m (hi.trans hik) hkm v']
      exact congrArg (fun q ↦ (J.sourceScalar k m (hi.trans hik) hkm).inv ≫ q ≫
        (J.targetScalar k m (hi.trans hik) hkm).hom) hm
    calc
      H.lift i hi u = H.lift m _ (H.transport k m _ hkm u') := by
        rw [H.refine, H.refine]
      _ = H.lift m _ (H.transport k m _ hkm v') := congrArg (H.lift m _) hf
      _ = H.lift j hj v := by rw [H.refine, H.refine]
  · intro g
    obtain ⟨i, hi, v, rfl⟩ := J.surjective g
    obtain ⟨u, hu⟩ := (hφ i hi).surjective v
    exact ⟨H.lift i hi u, by rw [hΦ, hu]⟩

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

private def finiteDualStageIso (B : Duality D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) (K : Stage l Ω X E) :
    ((stageSystem l Ω X).T h).obj ((B.finite.datum E).dual.obj (op K)) ≅
      (B.finite.datum L).dual.obj (op (((stageSystem l Ω X).T h).obj K)) :=
  (operationStageTransitionIso l Ω X E L h).app _ ≪≫
    (B.finite.beta E L h).app (op K) ≪≫
      (B.finite.datum L).dual.mapIso ((operationStageTransitionIso l Ω X E L h).app K).op

private def finiteOmegaStageIso (B : Duality D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    ((stageSystem l Ω X).T h).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (B.finite.omega E).omega) ≅
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
        (B.finite.omega L).omega :=
  (operationStageTransitionIso l Ω X E L h).app _ ≪≫ (B.finite.scalar E L h).omega

private theorem finiteOmegaStageIso_compatible (B : Duality D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    (inclusion L).map (finiteOmegaStageIso D l hl Ω X B h).hom ≫
        (B.omegaComparison L).hom =
      ((stageSystem l Ω X).transIso h).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom := by
  simpa only [finiteOmegaStageIso, Iso.trans_hom, Iso.app] using
    (finite_dual_inclusion_coherent D l hl Ω X B).2 h

private theorem finiteDualObject_compatible (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    {E L : Index l Ω} (hi : K.stage ≤ E) (h : E ≤ L) :
    (inclusion L).map
        ((finiteDualStageIso D l hl Ω X B h (K.toStage hi)).hom ≫
          (B.finite.datum L).dual.map
            (((stageSystem l Ω X).assoc hi h).inv.app K.obj).op) ≫
        (B.comparison L).hom.app (op (K.toStage (hi.trans h))) ≫
        B.duality.dual.map (((stageSystem l Ω X).isoToStage K (hi.trans h)).hom).op =
      ((stageSystem l Ω X).transIso h).hom.app
          ((B.finite.datum E).dual.obj (op (K.toStage hi))) ≫
        (B.comparison E).hom.app (op (K.toStage hi)) ≫
        B.duality.dual.map (((stageSystem l Ω X).isoToStage K hi).hom).op := by
  simpa only [finiteDualStageIso, Iso.trans_hom, Iso.app, Functor.mapIso_hom,
    Iso.op_hom, Category.assoc] using
    (finite_dual_inclusion_coherent D l hl Ω X B).1 K hi h

/-- The finite evaluation transpose descends along a chosen comparison.
Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
(blueprint: lem-coef-qbar-verdier-internal-hom-universal).
Proof: represent both arguments and a morphism at a common compositum stage.
`finite_evaluation_transpose_bijective` gives inverse maps there. The scalar
comparison and the normalized evaluation square preserve eventual equality, so
these inverse maps descend to the common-stage Hom groups. -/
theorem internal_hom_universal_of_comparison
    (B : Duality D l hl Ω X)
    (permitted : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
      commonStageHomPairs l Ω X (op K, B.omega))
    (_comparison : B.duality.dual ≅ homDual l Ω X B.omega permitted)
    (hproperties : DualityProperties D l hl Ω X B.val) :
    ∀ (K P : generalAlgebraicallyClosedConstructibleCategory l Ω X),
      Function.Bijective (fun h : P ⟶ B.duality.dual.obj (op K) ↦
        (CoefQbarTensor D l hl Ω X).map (Prod.mkHom (𝟙 K) h) ≫ B.evaluation K) := by
  let := RationalVerdier.units D l hl X
  let B : Duality D l hl Ω X := ⟨B.val, hproperties⟩
  intro K P
  let S := stageSystem l Ω X
  let E := Padic.finiteCoefficientCompositum l Ω K.stage P.stage
  have hK : K.stage ≤ E := ((Padic.finiteCoefficientFields_properties l Ω).1 _ _).1
  have hP : P.stage ≤ E := ((Padic.finiteCoefficientFields_properties l Ω).1 _ _).2
  let H : HomStages S E P (B.duality.dual.obj (op K)) := {
    source := fun i hi ↦ P.toStage (hP.trans hi)
    target := fun i hi ↦ (B.finite.datum i).dual.obj (op (K.toStage (hK.trans hi)))
    sourceIso := fun i hi ↦ (S.isoToStage P (hP.trans hi)).symm
    targetIso := fun i hi ↦ (B.comparison i).app (op (K.toStage (hK.trans hi))) ≪≫
      B.duality.dual.mapIso (S.isoToStage K (hK.trans hi)).op
    sourceScalar := fun i j hi h ↦ (S.assoc (hP.trans hi) h).app P.obj
    targetScalar := fun i j hi h ↦
      finiteDualStageIso D l hl Ω X B h (K.toStage (hK.trans hi)) ≪≫
        (B.finite.datum j).dual.mapIso ((S.assoc (hK.trans hi) h).app K.obj).symm.op
    source_compatible := fun i j hi h ↦
      isoToStage_compatible S P (hP.trans hi) h
    target_compatible := by
      intro i j hi h
      exact finiteDualObject_compatible D l hl Ω X B K (hK.trans hi) h }
  let J : HomStages S E ((CoefQbarTensor D l hl Ω X).obj (K, P)) B.omega := {
    source := fun i hi ↦ (rationalDerivedTensor l (Coefficient.{u} l Ω i) X).obj
      (K.toStage (hK.trans hi), P.toStage (hP.trans hi))
    target := fun i _ ↦ (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω i) X).obj
      (B.finite.omega i).omega
    sourceIso := fun i hi ↦
      tensorInclusion D l hl Ω X i (K.toStage (hK.trans hi)) (P.toStage (hP.trans hi)) ≪≫
        (CoefQbarTensor D l hl Ω X).mapIso (Iso.prod
          (S.isoToStage K (hK.trans hi)).symm (S.isoToStage P (hP.trans hi)).symm)
    targetIso := fun i _ ↦ B.omegaComparison i
    sourceScalar := fun i j hi h ↦
      (rationalTensorStageComparison l Ω X h).app
        (K.toStage (hK.trans hi), P.toStage (hP.trans hi)) ≪≫
      (rationalDerivedTensor l (Coefficient.{u} l Ω j) X).mapIso (Iso.prod
        ((S.assoc (hK.trans hi) h).app K.obj) ((S.assoc (hP.trans hi) h).app P.obj))
    targetScalar := fun i j _ h ↦ finiteOmegaStageIso D l hl Ω X B h
    source_compatible := by
      intro i j hi h
      exact (finite_evaluation_representatives D l hl Ω X B).2.2 K P
        (hK.trans hi) (hP.trans hi) h
    target_compatible := fun i j hi h ↦ finiteOmegaStageIso_compatible D l hl Ω X B h }
  let φ (i : Index l Ω) (hi : E ≤ i) :
      (H.source i hi ⟶ H.target i hi) → (J.source i hi ⟶ J.target i hi) := fun f ↦
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω i)).map
      (Prod.mkHom (𝟙 (K.toStage (hK.trans hi))) f) ≫
        (B.finite.datum i).evaluation (K.toStage (hK.trans hi))
  apply stageEvaluationBijective H J φ
  · intro i hi
    exact (finite_evaluation_representatives D l hl Ω X B).1 i
      (K.toStage (hK.trans hi)) (P.toStage (hP.trans hi))
  · intro i j hi h f
    simpa only [φ, H, J, HomStages.transport, finiteDualStageIso, finiteOmegaStageIso,
      Iso.trans_hom, Iso.trans_inv,
      Iso.app, Functor.mapIso_hom, Functor.mapIso_inv, Iso.op_hom,
      Iso.symm_hom, Iso.symm_inv, Category.assoc] using
      finite_evaluation_transport_stages D l hl Ω X B.finite h
        (K.toStage (hK.trans hi)) (P.toStage (hP.trans hi))
        ((S.assoc (hK.trans hi) h).app K.obj)
        ((S.assoc (hP.trans hi) h).app P.obj) f
  · intro i hi f
    have he := (finite_evaluation_representatives D l hl Ω X B).2.1 K P i
      (hK.trans hi) (hP.trans hi) f
    simpa only [HomStages.lift, stageHomLift, H, J, φ, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.op_hom, Iso.prod_inv, Iso.prod_hom, Category.assoc] using he

end WeilConjectures.CoefQbarVerdier
