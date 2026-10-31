/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Compact.CompactSupportTargetRationalComparison
import WeilConjectures.CategoryTheory.StageSystem.StageSystemTargetComparison
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink

/-! The geometric stagewise comparison underlying target transport.

This is the finite/common-stage part of the target-isomorphism theorem
`(blueprint: lem-sf-constructible-compact-support-target-stage-comparison)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
open GeneralAlgebraicallyClosedCoefficients

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local irreducible] ScalarLocalization.category HasDerivedCategory.standard
  Padic.coefficientExtensionIntegers rationalDerivedPullback sfRationalScalarExtension
  ObjectProperty.FullSubcategory.category
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage category Shrink.instField Shrink.instAlgebra

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

private theorem relabel_transition
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Fj : B ⥤ D) (FΩ : E ⥤ H)
    (TX TX' : A ⥤ B) (TY TY' : C ⥤ D) (hx : TX = TX') (hy : TY = TY')
    (IXi : A ⥤ E) (IXj : B ⥤ E) (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY' ≅ TX' ⋙ Fj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi) (K : A)
    (hc : IYj.map (q.hom.app K) ≫ qj.hom.app (TX'.obj K) =
      (eqToIso (congrArg (fun T ↦ T ⋙ IYj) hy.symm) ≪≫ tauY).hom.app (Fi.obj K) ≫
        qi.hom.app K ≫ FΩ.map
          ((eqToIso (congrArg (fun T ↦ T ⋙ IXj) hx.symm) ≪≫ tauX).inv.app K)) :
    IYj.map ((Functor.isoWhiskerLeft Fi (eqToIso hy) ≪≫ q ≪≫
        Functor.isoWhiskerRight (eqToIso hx).symm Fj).hom.app K) ≫
        qj.hom.app (TX.obj K) =
      tauY.hom.app (Fi.obj K) ≫ qi.hom.app K ≫ FΩ.map (tauX.inv.app K) := by
  cases hx
  cases hy
  simpa using hc

private theorem common_operation_transition
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (S : System.{u, v} l Ω D hl (f := f)) (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j)
    (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (commonInclusion l Ω Y j).map
        ((rationalOperationTransition l Ω D hl S.ring S.fields c hij).hom.app K) ≫
        (S.common.commonComparison c j).q.hom.app (((stageSystem l Ω X).T hij).obj K) =
      ((stageSystem l Ω Y).transIso hij).hom.app
          ((S.ring.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K) ≫
        (S.common.commonComparison c i).q.hom.app K ≫
        (S.ring.operation c .closed).F.map
          (((stageSystem l Ω X).transIso hij).inv.app K) := by
  have hx : (stageSystem l Ω X).T hij = transition l Ω X i j hij := by
    unfold stageSystem
    exact (stageSystem_existsUnique l Ω X).exists.choose_spec.1 i j hij
  have hy : (stageSystem l Ω Y).T hij = transition l Ω Y i j hij := by
    unfold stageSystem
    exact (stageSystem_existsUnique l Ω Y).exists.choose_spec.1 i j hij
  have hc := S.common.commonCocycleLeft c i j hij K
  unfold commonTransition at hc
  exact relabel_transition _ _ _ _ _ _ _ hx hy _ _ _ _
    (S.fields.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{max u v} l Ω i j hij)).q
    (S.common.commonComparison c i).q (S.common.commonComparison c j).q
    ((stageSystem l Ω X).transIso hij) ((stageSystem l Ω Y).transIso hij) K
    (by simpa only [stageSystem, transition, rationalScalar] using eq_of_heq hc)

attribute [local irreducible] rationalOperationTransition commonStagePullbackTransition
  commonStageDerivedPullback StageSystem.Morphism.functor

/-- Stagewise compact-support comparison after an isomorphism of targets.
Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, final
exceptional-adjunction sentence, finite-stage and common-stage comparison paragraphs.
The theorem records the geometric proper/open comparison and its coefficient descent
on every common finite stage; assembling it over the pair category is separate.
(blueprint: lem-sf-constructible-compact-support-target-stage-comparison).
-/
theorem constructible_compact_support_target_stage_comparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{max u v}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (S : System.{u, v} l Ω D hl (f := f)) (c : Compactification f)
    (S' : System.{u, v} l Ω D hl (f := g)) (c' : Compactification g) :
    ∃ (q : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      commonInclusion l Ω X i ⋙ (S.ring.operation c .closed).F ≅
        commonInclusion l Ω X i ⋙
          ((S'.ring.operation c' .closed).F ⋙ commonStageDerivedPullback l Ω e.hom)),
      ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j)
        (K : C.{u, v} l Ω X (.rational (commonField l Ω i))),
        (S.ring.operation c .closed).F.map
            (((stageSystem l Ω X).transIso hij).inv.app K) ≫
            (q j).hom.app (((stageSystem l Ω X).T hij).obj K) =
          (q i).hom.app K ≫
            ((S'.ring.operation c' .closed).F ⋙
              commonStageDerivedPullback l Ω e.hom).map
                (((stageSystem l Ω X).transIso hij).inv.app K) := by
  obtain ⟨a, ha⟩ := compact_support_target_rational_comparison
    l Ω D hl f g e h S.ring S.fields c S'.ring S'.fields c'
  obtain ⟨hcoh, hH⟩ := commonStagePullbackNormalizedDescent l Ω e.hom
  rw [hH]
  let P : (stageSystem l Ω Z).Morphism (stageSystem l Ω Y) :=
    ⟨fun i ↦ rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω i) e.hom,
      commonStagePullbackTransition l Ω e.hom, hcoh⟩
  exact StageSystem.assembleTargetComparison (stageSystem l Ω X) (stageSystem l Ω Y)
    (stageSystem l Ω Z) (S.ring.operation c .closed).F (S'.ring.operation c' .closed).F P
    (fun i ↦ (S.ring.operation c (.rational (commonField.{u, v} l Ω i))).F)
    (fun i ↦ (S'.ring.operation c' (.rational (commonField.{u, v} l Ω i))).F)
    (fun hij ↦ rationalOperationTransition l Ω D hl S.ring S.fields c hij)
    (fun hij ↦ rationalOperationTransition l Ω D hl S'.ring S'.fields c' hij)
    (fun i ↦ (S.common.commonComparison c i).q)
    (fun i ↦ (S'.common.commonComparison c' i).q)
    (fun hij ↦ common_operation_transition l Ω D hl S c hij)
    (fun hij ↦ common_operation_transition l Ω D hl S' c' hij) a ha

end WeilConjectures.ConstructibleExceptionalCoefficients
