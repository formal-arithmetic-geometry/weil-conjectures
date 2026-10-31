/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! Compatibility of finite duality inclusions with scalar extension. -/

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

private theorem isoToStage_compatible_inv
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
    (P : S.PairCategory) {i j : I} (hi : P.stage ≤ i) (h : i ≤ j) :
    (S.isoToStage P (hi.trans h)).hom ≫ (S.ι j).map ((S.assoc hi h).inv.app P.obj) =
      (S.isoToStage P hi).hom ≫ (S.transIso h).inv.app (P.toStage hi) := by
  have he : (S.ι j).mapIso ((S.assoc hi h).app P.obj) ≪≫
        (S.isoToStage P (hi.trans h)).symm =
      (S.transIso h).app (P.toStage hi) ≪≫ (S.isoToStage P hi).symm :=
    Iso.ext (isoToStage_compatible S P hi h)
  exact congrArg Iso.inv he

private theorem whisker_eqToIso
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    {F G : C ⥤ D} (h : F = G) (J : D ⥤ E) :
    eqToIso (congrArg (fun H : C ⥤ D ↦ H ⋙ J) h) =
      Functor.isoWhiskerRight (eqToIso h) J := by
  subst G
  apply Iso.ext
  ext X
  simp

private theorem dualityScalarOfEq
    {C : Type*} [Category C] {D : Type*} [Category D] {A : Type*} [Category A]
    (F G : C ⥤ D) (h : F = G) (I : C ⥤ A) (J : D ⥤ A)
    (t : F ⋙ J ≅ I) (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D) (g : Aᵒᵖ ⥤ A)
    (β : d ⋙ G ≅ G.op ⋙ e) (a : d ⋙ I ≅ I.op ⋙ g) (b : e ⋙ J ≅ J.op ⋙ g)
    (hc : ∀ K,
      J.map (β.hom.app (op K)) ≫ b.hom.app (op (G.obj K)) ≫
          g.map (((Functor.isoWhiskerRight (eqToIso h).symm J ≪≫ t).inv.app K).op) =
        (Functor.isoWhiskerRight (eqToIso h).symm J ≪≫ t).hom.app (d.obj (op K)) ≫
          a.hom.app (op K)) (K : C) :
    J.map ((eqToIso h).hom.app (d.obj (op K)) ≫ β.hom.app (op K) ≫
        e.map ((eqToIso h).hom.app K).op) ≫ b.hom.app (op (F.obj K)) ≫
        g.map (t.inv.app K).op = t.hom.app (d.obj (op K)) ≫ a.hom.app (op K) := by
  subst G
  simpa using hc K

private theorem omegaScalarOfEq
    {C : Type*} [Category C] {D : Type*} [Category D] {A : Type*} [Category A]
    (F G : C ⥤ D) (h : F = G) (I : C ⥤ A) (J : D ⥤ A)
    (t : F ⋙ J ≅ I) (w : C) (z : D) (o : A)
    (β : G.obj w ≅ z) (a : I.obj w ≅ o) (b : J.obj z ≅ o)
    (hc : J.map β.hom ≫ b.hom =
      (Functor.isoWhiskerRight (eqToIso h).symm J ≪≫ t).hom.app w ≫ a.hom) :
    J.map ((eqToIso h).hom.app w ≫ β.hom) ≫ b.hom = t.hom.app w ≫ a.hom := by
  subst G
  simpa using hc

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

private theorem inclusionTransition_eq (E L : Index l Ω) (h : E ≤ L) :
    inclusionTransition l Ω X E L h =
      Functor.isoWhiskerRight (operationStageTransitionIso l Ω X E L h).symm
        (inclusion L) ≪≫ (stageSystem l Ω X).transIso h := by
  unfold inclusionTransition operationStageTransitionIso
  rw [whisker_eqToIso
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h).symm]
  rfl

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

private theorem finiteDualStageIso_compatible (B : Duality D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) (K : Stage l Ω X E) :
    (inclusion L).map (finiteDualStageIso D l hl Ω X B h K).hom ≫
        (B.comparison L).hom.app (op (((stageSystem l Ω X).T h).obj K)) ≫
        B.duality.dual.map (((stageSystem l Ω X).transIso h).inv.app K).op =
      ((stageSystem l Ω X).transIso h).hom.app ((B.finite.datum E).dual.obj (op K)) ≫
        (B.comparison E).hom.app (op K) := by
  have hc := B.property.2.2.2.2.2.2.1
  have he := dualityScalarOfEq ((stageSystem l Ω X).T h)
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h)
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h)
    (inclusion E) (inclusion L) ((stageSystem l Ω X).transIso h)
    (B.finite.datum E).dual (B.finite.datum L).dual B.duality.dual
    (B.finite.beta E L h) (B.comparison E) (B.comparison L)
    (fun M ↦ by simpa only [inclusionTransition_eq, operationStageTransitionIso] using hc E L h M) K
  simpa only [finiteDualStageIso, Iso.trans_hom, Iso.app, Functor.mapIso_hom,
    Iso.op_hom, operationStageTransitionIso, Category.assoc] using he

private theorem finiteOmegaStageIso_compatible (B : Duality D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    (inclusion L).map (finiteOmegaStageIso D l hl Ω X B h).hom ≫
        (B.omegaComparison L).hom =
      ((stageSystem l Ω X).transIso h).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom := by
  have hc := B.property.2.2.2.2.2.2.2.2.1
  have he := omegaScalarOfEq ((stageSystem l Ω X).T h)
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h)
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h)
    (inclusion E) (inclusion L) ((stageSystem l Ω X).transIso h)
    _ _ B.omega (B.finite.scalar E L h).omega
    (B.omegaComparison E) (B.omegaComparison L)
    (by simpa only [inclusionTransition_eq, operationStageTransitionIso] using hc E L h)
  simpa only [finiteOmegaStageIso, Iso.trans_hom, Iso.app,
    operationStageTransitionIso] using he

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
  have hn := (B.comparison L).hom.naturality
    (((stageSystem l Ω X).assoc hi h).inv.app K.obj).op
  dsimp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hn
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn]
  rw [← B.duality.dual.map_comp, ← op_comp,
    isoToStage_compatible_inv (stageSystem l Ω X) K hi h,
    op_comp, B.duality.dual.map_comp]
  rw [reassoc_of% (finiteDualStageIso_compatible D l hl Ω X B h (K.toStage hi))]

/-- Finite dual and dualizing-object inclusions commute with coefficient extension.
Source: blueprint thm-coef-qbar-verdier, scalar comparison in evaluation descent.
(blueprint: lem-coef-qbar-dual-inclusion-coherent).
Proof: first transport the recorded finite dual and dualizing-object squares along
its equality between the stage transition and the prescribed scalar functor.
Equality induction proves this transport with the indicated endpoint corrections.
For an arbitrary common-stage representative, naturality of the finite dual
comparison moves the stage associator through it. The composition identity for
isoToStage identifies the resulting global dual morphism with the original one.
The argument includes repeated coefficient fields and needs no faithful transition. -/
theorem finite_dual_inclusion_coherent (B : Duality D l hl Ω X) :
    (∀ (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    {E L : Index l Ω} (hi : K.stage ≤ E) (h : E ≤ L),
    (inclusion L).map
        (((operationStageTransitionIso l Ω X E L h).hom.app
            ((B.finite.datum E).dual.obj (op (K.toStage hi))) ≫
          (B.finite.beta E L h).hom.app (op (K.toStage hi)) ≫
          (B.finite.datum L).dual.map
            ((operationStageTransitionIso l Ω X E L h).hom.app (K.toStage hi)).op) ≫
          (B.finite.datum L).dual.map
            (((stageSystem l Ω X).assoc hi h).inv.app K.obj).op) ≫
        (B.comparison L).hom.app (op (K.toStage (hi.trans h))) ≫
        B.duality.dual.map (((stageSystem l Ω X).isoToStage K (hi.trans h)).hom).op =
      ((stageSystem l Ω X).transIso h).hom.app
          ((B.finite.datum E).dual.obj (op (K.toStage hi))) ≫
        (B.comparison E).hom.app (op (K.toStage hi)) ≫
        B.duality.dual.map (((stageSystem l Ω X).isoToStage K hi).hom).op) ∧
    (∀ {E L : Index l Ω} (h : E ≤ L),
    (inclusion L).map ((operationStageTransitionIso l Ω X E L h).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫ (B.finite.scalar E L h).omega.hom) ≫
        (B.omegaComparison L).hom =
      ((stageSystem l Ω X).transIso h).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom) := by
  constructor
  · intro K E L hi h
    simpa only [finiteDualStageIso, Iso.trans_hom, Iso.app, Functor.mapIso_hom,
      Iso.op_hom, Category.assoc] using
      finiteDualObject_compatible D l hl Ω X B K hi h
  · intro E L h
    simpa only [finiteOmegaStageIso, Iso.trans_hom, Iso.app] using
      finiteOmegaStageIso_compatible D l hl Ω X B h

end WeilConjectures.CoefQbarVerdier
