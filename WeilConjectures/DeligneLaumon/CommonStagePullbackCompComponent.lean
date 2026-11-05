/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompData
public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponentAux
import WeilConjectures.TraceFormula.Integral.IntegralPullbackCompositionScalarRational
import all Mathlib.Logic.Small.Defs

/-! # Common-stage pullback composition component

(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] commonStagePullbackCompComponent
  commonStageDerivedPullback constructibleIntegralPullback

-- Use the same cached categories as the existing normalized compositor API.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

set_option allowUnsafeReducibility true in
attribute [local irreducible] ScalarLocalization.composition
  GeneralAlgebraicallyClosedCoefficients.ofHom StageSystem.PairCategory.mkHom
  rationalDerivedPullback commonStagePullbackComparison
  commonStagePullbackRationalComposition HasDerivedCategory.standard integralCoefficientLinear
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence Scheme.residueField

set_option allowUnsafeReducibility true in
attribute [local reducible] rationalDerivedPullback

private theorem normalization_map_heq
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hA
  cases hB
  cases h
  rfl

/-- Cancellation of the inserted comparison isomorphisms in a conjugated square. -/
private theorem stage_square_cancel {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B A' B' W W' : D} {U U' V V' : C}
    (x : A ⟶ B) (m : B ⟶ B') (y : A' ≅ B') (ρP : B ⟶ G.obj U) (ρQ : B' ⟶ G.obj U')
    (zP : V ≅ U) (zQ : V' ≅ U') (wP : W ≅ G.obj V) (wQ : W' ≅ G.obj V') (n : U ⟶ U')
    (h : ρP ≫ G.map n = m ≫ ρQ) :
    (x ≫ m ≫ y.inv) ≫ (y.hom ≫ ρQ ≫ G.map zQ.inv ≫ wQ.inv) =
      (x ≫ ρP ≫ G.map zP.inv ≫ wP.inv) ≫
        (wP.hom ≫ G.map (zP.hom ≫ n ≫ zQ.inv) ≫ wQ.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp,
    Iso.map_inv_hom_id_assoc, reassoc_of% h]

/-- The conjugated fixed-stage square underlying common-stage naturality.
Source: Stacks 099N(5), finite-stage cancellation after coefficient compatibility.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the stage-category equality obtained after inserting the three pullback
comparison isomorphisms; the common-stage wrapper is handled by the parent theorem.
Proof: cancel the inner comparison of `f ≫ g` at `Q` and the comparison of `f` at the
pullback of `P`, expand the pullback of the composite map by functoriality, and apply the
fixed-stage rational naturality. -/
theorem commonStagePullbackCompComponent_stage_square
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map r ≫
      (commonStagePullbackComparison l Ω (f ≫ g) Q L hQ).inv) ≫
      ((commonStagePullbackComparison l Ω (f ≫ g) Q L hQ).hom ≫
        (commonStagePullbackRationalComposition l Ω f g L Q hQ).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g Q L hQ).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g Q) L hQ).inv) =
      ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
        (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g P) L hP).inv) ≫
      ((commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g P) L hP).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g P L hP).hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map r ≫
            (commonStagePullbackComparison l Ω g Q L hQ).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g Q) L hQ).inv) := by
  exact stage_square_cancel
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
    (commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom
    ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map r)
    (commonStagePullbackComparison l Ω (f ≫ g) Q L hQ)
    (commonStagePullbackRationalComposition l Ω f g L P hP).hom
    (commonStagePullbackRationalComposition l Ω f g L Q hQ).hom
    (commonStagePullbackComparison l Ω g P L hP)
    (commonStagePullbackComparison l Ω g Q L hQ)
    (commonStagePullbackComparison l Ω f (commonStagePullbackObject l Ω g P) L hP)
    (commonStagePullbackComparison l Ω f (commonStagePullbackObject l Ω g Q) L hQ)
    ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map r)
    (commonStagePullbackRationalComposition_naturality l Ω f g L hP hQ r)

/-- The selected common-stage component is represented at every larger coefficient stage.
Source: Stacks 099N(5), coefficient-compatibility argument in residue-compatible pullback.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the scalar-extension transport of the chosen integral compositor; it is the
finite-stage calculation used by the naturality proof.
Proof: by the object representation both sides are arrows of the pair category between the
same literal objects. The left side is represented at `P.stage` by the localized integral
compositor at `P.stage`, i.e. by the fixed-stage rational compositor. Enlarging that
representative to `L` applies the coefficient transition `P.stage ≤ L`
(StageSystem.ι_map_eq). The recorded transitions are the rational scalar extensions, and
rationalPullbackComposition_scalar_transport (from integralPullbackComposition_scalar: the
compositor is pinned by its system-level reduction, on which scalar extension acts
compatibly) carries the `P.stage` compositor to the `L` compositor conjugated by exactly the
three `commonStagePullbackComparison` factors; the literal equality transports cancel by
proof irrelevance. -/
theorem commonStagePullbackCompComponent_stage_representation
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) :
    HEq (commonStagePullbackCompComponent l Ω f g P).hom
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω (f ≫ g) P)
        (commonStagePullbackObject l Ω f
          (commonStagePullbackObject l Ω g P)) L hP hP
        ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
          (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
            ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
          (commonStagePullbackComparison l Ω f
            (commonStagePullbackObject l Ω g P) L hP).inv)) := by
  have h0 := commonStagePullbackCompComponent_heq l Ω f g P
  have hw := rationalPullbackCompositionIso_heq l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g P.obj
  have eA : (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).obj
        ((constructibleIntegralPullback l _ (f ≫ g)).obj P.obj.obj) =
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) (f ≫ g)).obj P.obj :=
    ((rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) (f ≫ g)).exists.choose_spec.2.1
        P.obj).symm
  have eB : (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).obj
        ((constructibleIntegralPullback l _ f).obj
          ((constructibleIntegralPullback l _ g).obj P.obj.obj)) =
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).obj
          ((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g).obj P.obj) :=
    ((congrArg (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).obj
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g).exists.choose_spec.2.1
          P.obj)).trans
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l _ Y).obj
          ((constructibleIntegralPullback l _ g).obj P.obj.obj)))).symm
  have h1 := normalization_map_heq
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage)
    eA eB hw.symm
  refine h0.trans (h1.trans (heq_of_eq ?_))
  have eX : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω X P.stage L hP := by
    simpa only [GeneralAlgebraicallyClosedCoefficients.stageSystem] using
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists.choose_spec.1
        P.stage L hP
  have eY : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Y P.stage L hP := by
    simpa only [GeneralAlgebraicallyClosedCoefficients.stageSystem] using
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).exists.choose_spec.1
        P.stage L hP
  have eZ : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Z P.stage L hP := by
    simpa only [GeneralAlgebraicallyClosedCoefficients.stageSystem] using
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Z).exists.choose_spec.1
        P.stage L hP
  have key := rationalPullbackComposition_scalar_transport l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L hP) f g
    _ _ _ eX eY eZ P.obj
  refine (StageSystem.ι_map_eq hP _).trans ?_
  have eR : commonStagePullbackRationalComposition l Ω f g L P hP =
      rationalPullbackCompositionIso l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f g
        (P.toStage hP) := by
    unfold commonStagePullbackRationalComposition rationalPullbackCompositionIso
    rfl
  rw [eR]
  unfold commonStagePullbackComparison
    operationStageTransitionIso GeneralAlgebraicallyClosedCoefficients.ofHom
  exact congrArg (StageSystem.PairCategory.mkHom (X := commonStagePullbackObject l Ω (f ≫ g) P)
      (Y := commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g P)) L hP hP) key

end WeilConjectures
