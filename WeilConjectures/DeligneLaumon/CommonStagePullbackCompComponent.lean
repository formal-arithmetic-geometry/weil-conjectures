/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompData

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

private theorem normalization_map_heq
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hA
  cases hB
  cases h
  rfl

private theorem rational_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {K J : sfRationalConstructibleCategory l E Z}
    (ρK : (rationalDerivedPullback l E (f ≫ g)).obj K ≅
      (rationalDerivedPullback l E f).obj ((rationalDerivedPullback l E g).obj K))
    (ρJ : (rationalDerivedPullback l E (f ≫ g)).obj J ≅
      (rationalDerivedPullback l E f).obj ((rationalDerivedPullback l E g).obj J))
    (hK : HEq ρK.hom ((sfRationalConstructibleLocalization l E X).map
      (((integralPullbackComposition l E).choose f g).hom.app K.obj)))
    (hJ : HEq ρJ.hom ((sfRationalConstructibleLocalization l E X).map
      (((integralPullbackComposition l E).choose f g).hom.app J.obj)))
    (v : K ⟶ J) :
    ρK.hom ≫ (rationalDerivedPullback l E f).map
        ((rationalDerivedPullback l E g).map v) =
      (rationalDerivedPullback l E (f ≫ g)).map v ≫ ρJ.hom := by
  have obj {V W : Scheme.{u}} (k : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E k).obj M =
        ⟨(constructibleIntegralPullback l E k).obj M.obj⟩ := by
    simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E k).exists.choose_spec.2.1 M
  have hom {V W : Scheme.{u}} (k : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfIntegralConstructibleCategory l E W) (b : M ⟶ N)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((rationalDerivedPullback l E k).map
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] b))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E k).map b) := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E k).exists.choose_spec.2.2 M N b c
  have : (rationalDerivedPullback l E (f ≫ g)).Additive := by
    simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E (f ≫ g)).exists.choose_spec.1
  have : (rationalDerivedPullback l E g).Additive := by
    simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.1
  have : (rationalDerivedPullback l E f).Additive := by
    simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have compobj (M) : (rationalDerivedPullback l E f).obj
      ((rationalDerivedPullback l E g).obj M) =
      ⟨(constructibleIntegralPullback l E f).obj
        ((constructibleIntegralPullback l E g).obj M.obj)⟩ := by
    rw [obj, obj]
  induction v with
  | tmul c a =>
    have hm := (normalization_map_heq (rationalDerivedPullback l E f)
      (obj g K) (obj g J)
      (hom g _ _ a c)).trans
        (hom f _ _ ((constructibleIntegralPullback l E g).map a) c)
    have hleft := heq_comp (obj (f ≫ g) K)
      (compobj K) (compobj J) hK hm
    have hright := heq_comp (obj (f ≫ g) K)
      (obj (f ≫ g) J) (compobj J)
      (hom (f ≫ g) _ _ a c) hJ
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ (constructibleIntegralPullback l E f).map
          ((constructibleIntegralPullback l E g).map a))
        (1 ⊗ₜ ((integralPullbackComposition l E).choose f g).hom.app K.obj) =
      ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ ((integralPullbackComposition l E).choose f g).hom.app J.obj)
        (c ⊗ₜ (constructibleIntegralPullback l E (f ≫ g)).map a)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun b ↦ c ⊗ₜ b)
      (((integralPullbackComposition l E).choose f g).hom.naturality a).symm
  | add a b ha hb =>
    change _ ≫ (rationalDerivedPullback l E f).map
        ((rationalDerivedPullback l E g).map (a + b : K ⟶ J)) =
      (rationalDerivedPullback l E (f ≫ g)).map
        (a + b : K ⟶ J) ≫ _
    rw [Functor.map_add, Functor.map_add, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add, ha, hb]

set_option allowUnsafeReducibility true in
attribute [local reducible] rationalDerivedPullback

/-- Naturality of the fixed-stage rational compositor on localized representatives.
Source: Stacks 099N(5), coefficient-compatibility calculation on pure tensors and additivity.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
The proof expands the chosen integral compositor on pure tensors, applies its integral
naturality, and extends by additivity. -/
theorem commonStagePullbackRationalComposition_naturality
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    {K J : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (hK : K.stage ≤ L) (hJ : J.stage ≤ L)
    (v : K.toStage hK ⟶ J.toStage hJ) :
    (commonStagePullbackRationalComposition l Ω f g L K hK).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map v) =
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map v ≫
        (commonStagePullbackRationalComposition l Ω f g L J hJ).hom := by
  have hc (M : generalAlgebraicallyClosedConstructibleCategory l Ω Z) (hM : M.stage ≤ L) :
      HEq (commonStagePullbackRationalComposition l Ω f g L M hM).hom
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).map
          (((integralPullbackComposition l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).choose f g).hom.app
            (M.toStage hM).obj)) := by
    unfold commonStagePullbackRationalComposition
    have ha := (rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).exists.choose_spec.2.1
      (M.toStage hM)
    have hb := (congrArg (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).exists.choose_spec.2.1
        (M.toStage hM))).trans
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y).obj
          ((constructibleIntegralPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).obj
            (M.toStage hM).obj)))
    exact (conj_eqToHom_iff_heq _ _ ha hb).mp rfl
  exact rational_naturality l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f g
    (commonStagePullbackRationalComposition l Ω f g L K hK)
    (commonStagePullbackRationalComposition l Ω f g L J hJ) (hc K hK) (hc J hJ) v

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
    Iso.inv_hom_id_map_assoc, reassoc_of% h]

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
  exact stage_square_cancel _ _ _ _ _ _ _ _ _ _ _
    (commonStagePullbackRationalComposition_naturality l Ω f g L hP hQ r)

/-- The selected common-stage component is represented at every larger coefficient stage.
Source: Stacks 099N(5), coefficient-compatibility argument in residue-compatible pullback.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the scalar-extension transport of the chosen integral compositor; it is the
finite-stage calculation used by the naturality proof.
Proof: by the object representation both sides are arrows of the pair category between the
same literal objects. The left side is represented at `P.stage` by the localized integral
compositor at `P.stage`. Enlarging that representative to `L` applies the coefficient
transition `P.stage ≤ L`, conjugated by the recorded stage-transition identifications.
The scalar-extension compatibility of integral pullback (pullback identities and scalar
extension) carries the `P.stage` compositor to the `L` compositor conjugated by the rational
pullback scalar comparisons of `f ≫ g`, `f` and `g`; the compositor is pinned by its finite
reductions, which are jointly faithful, so the two compositors agree. These comparisons,
with the transition identifications, are exactly the three `commonStagePullbackComparison`
factors, and the literal equality transports cancel by proof irrelevance. -/
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
  sorry

end WeilConjectures
