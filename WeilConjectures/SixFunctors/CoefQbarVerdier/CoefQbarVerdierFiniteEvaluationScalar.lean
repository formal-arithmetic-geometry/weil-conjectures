/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFiniteEvaluationStage

/-! The normalized evaluation square in the named coefficient stage system. -/

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

private theorem evaluation_scalar_formula
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F : C ⥤ D)
    (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D) (w : C) (z : D)
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, U.obj (K, e.obj (op K)) ⟶ z)
    (t : T ⋙ F ≅ F.prod F ⋙ U)
    (β : ∀ K, F.obj (d.obj (op K)) ≅ e.obj (op (F.obj K))) (ω : F.obj w ≅ z)
    (he : ∀ K, U.map (Prod.mkHom (𝟙 (F.obj K)) ((β K).hom)) ≫ ew (F.obj K) =
      t.inv.app (K, d.obj (op K)) ≫ F.map (ev K) ≫ ω.hom)
    (K P : C) (h : P ⟶ d.obj (op K)) :
    U.map (Prod.mkHom (𝟙 (F.obj K)) (F.map h ≫ (β K).hom)) ≫ ew (F.obj K) =
      t.inv.app (K, P) ≫ F.map (T.map (Prod.mkHom (𝟙 K) h) ≫ ev K) ≫ ω.hom := by
  calc
    _ = U.map (Prod.mkHom (𝟙 (F.obj K)) (F.map h)) ≫
        (U.map (Prod.mkHom (𝟙 (F.obj K)) ((β K).hom)) ≫ ew (F.obj K)) := by
          rw [← U.map_comp_assoc]
          congr 2
          simp
    _ = _ := by
      rw [he]
      have ht := t.inv.naturality (Prod.mkHom (𝟙 K) h)
      simp only [Functor.comp_map, Functor.prod_map] at ht
      rw [F.map_id] at ht
      rw [reassoc_of% ht]
      simp only [Functor.map_comp, Category.assoc]

private theorem evaluation_transport
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F : C ⥤ D)
    (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D) (w : C) (z : D)
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, U.obj (K, e.obj (op K)) ⟶ z)
    (hn : ∀ {K M} (f : K ⟶ M), U.map (Prod.mkHom f (𝟙 _)) ≫ ew M =
      U.map (Prod.mkHom (𝟙 K) (e.map f.op)) ≫ ew K)
    (t : T ⋙ F ≅ F.prod F ⋙ U)
    (β : ∀ K, F.obj (d.obj (op K)) ≅ e.obj (op (F.obj K))) (ω : F.obj w ≅ z)
    (he : ∀ K, U.map (Prod.mkHom (𝟙 (F.obj K)) ((β K).hom)) ≫ ew (F.obj K) =
      t.inv.app (K, d.obj (op K)) ≫ F.map (ev K) ≫ ω.hom)
    (K P : C) {K' P' : D} (a : F.obj K ≅ K') (b : F.obj P ≅ P')
    (h : P ⟶ d.obj (op K)) :
    U.map (Prod.mkHom (𝟙 K')
      (b.inv ≫ F.map h ≫ (β K).hom ≫ e.map a.inv.op)) ≫ ew K' =
      (U.mapIso (Iso.prod a b)).inv ≫ t.inv.app (K, P) ≫
        F.map (T.map (Prod.mkHom (𝟙 K) h) ≫ ev K) ≫ ω.hom := by
  have hi := evaluation_iso_formula U e z ew hn a.symm b.symm
    (F.map h ≫ (β K).hom)
  simp only [Iso.symm_hom, Category.assoc] at hi
  rw [hi, evaluation_scalar_formula T U F d e w z ev ew t β ω he]
  rfl

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
attribute [local implicit_reducible] Stage
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.uniformProd
  GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- Finite evaluation commutes with coefficient extension and endpoint isomorphisms.
Source: blueprint thm-coef-qbar-verdier, evaluation descent in step 5.
(blueprint: lem-coef-qbar-finite-evaluation-stage-scalar).
Proof: transport the normalized finite evaluation square along the recorded
transition equality. Naturality of the tensor comparison moves the extended
morphism through that square. Naturality of evaluation in the first variable
then transports along a inverse, while functoriality transports along b inverse.
Combining these equalities gives precisely the displayed tensor comparison,
endpoint comparison, and dualizing-object comparison. This also applies to
identity coefficient extensions and arbitrary isomorphisms a and b. -/
theorem finite_evaluation_transport_stages (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) (K P : Stage l Ω X E)
    {K' P' : Stage l Ω X L}
    (a : ((stageSystem l Ω X).T h).obj K ≅ K')
    (b : ((stageSystem l Ω X).T h).obj P ≅ P')
    (f : P ⟶ (F.datum E).dual.obj (op K)) :
    letI := RationalVerdier.units D l hl X
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L)).map
      (Prod.mkHom (𝟙 K') (b.inv ≫ ((stageSystem l Ω X).T h).map f ≫
        ((operationStageTransitionIso l Ω X E L h).hom.app
            ((F.datum E).dual.obj (op K)) ≫ (F.beta E L h).hom.app (op K) ≫
          (F.datum L).dual.map ((operationStageTransitionIso l Ω X E L h).hom.app K).op) ≫
          (F.datum L).dual.map a.inv.op)) ≫ (F.datum L).evaluation K' =
      ((rationalDerivedTensor l (Coefficient.{u} l Ω L) X).mapIso (Iso.prod a b)).inv ≫
        (rationalTensorStageComparison l Ω X h).inv.app (K, P) ≫
          ((stageSystem l Ω X).T h).map
            ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).map
              (Prod.mkHom (𝟙 K) f) ≫ (F.datum E).evaluation K) ≫
            ((operationStageTransitionIso l Ω X E L h).hom.app
              ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
                (F.omega E).omega) ≫ (F.scalar E L h).omega.hom)  := by
  let := RationalVerdier.units D l hl X
  let β (M : Stage l Ω X E) :=
    (operationStageTransitionIso l Ω X E L h).app ((F.datum E).dual.obj (op M)) ≪≫
      (F.beta E L h).app (op M) ≪≫
        (F.datum L).dual.mapIso ((operationStageTransitionIso l Ω X E L h).app M).op
  let ω := (operationStageTransitionIso l Ω X E L h).app
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (F.omega E).omega) ≪≫ (F.scalar E L h).omega
  have he (M : Stage l Ω X E) :
      (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L)).map
          (Prod.mkHom (𝟙 (((stageSystem l Ω X).T h).obj M)) (β M).hom) ≫
          (F.datum L).evaluation (((stageSystem l Ω X).T h).obj M) =
        (rationalTensorStageComparison l Ω X h).inv.app (M, (F.datum E).dual.obj (op M)) ≫
          ((stageSystem l Ω X).T h).map ((F.datum E).evaluation M) ≫ ω.hom := by
    simpa only [β, ω, Iso.trans_hom, Iso.app, Functor.mapIso_hom, Iso.op_hom,
      Category.assoc] using finite_evaluation_scalar_of_stages D l hl Ω X F h M
  have hh := evaluation_transport (C := Stage l Ω X E) (D := Stage l Ω X L)
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E))
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L))
    ((stageSystem l Ω X).T h) (F.datum E).dual (F.datum L).dual
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj (F.omega E).omega)
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj (F.omega L).omega)
    (F.datum E).evaluation (F.datum L).evaluation
    (fun {_ _} f ↦ (F.datum L).evaluation_natural _ _ f)
    (rationalTensorStageComparison l Ω X h) β ω he K P a b f
  simpa only [β, ω, Iso.trans_hom, Iso.app, Functor.mapIso_hom, Iso.op_hom,
    Category.assoc] using hh

end WeilConjectures.CoefQbarVerdier
