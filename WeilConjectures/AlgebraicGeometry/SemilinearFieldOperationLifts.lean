/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.IsomorphismDerivedPullback
public import WeilConjectures.AlgebraicGeometry.PullbackIdentitiesScalarExtension
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackComposition
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport

/-! # Semilinear Frobenius transport and field-operation lifts

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 1; sec-six-functors/sk-rem-sf-pf-done,
lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-semilinear-field-operation-lifts).

The fixed-pair functors are the existing IsoAlgebra transports. The specifications
record their object, structure and arrow formulas. Partial internal Hom retains
its precise permitted-pair domain. Exactness refers to underlying derived functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry Opposite
open CategoryTheory.SuppliedExchangeProjection
open scoped TensorProduct
namespace WeilConjectures

/-- The explicit covariant formula, including its intertwining equation and the
forgetful equality. Source: blueprint prop-weil-operations, proof sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodCovariantWeilLiftSpec
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} (F : C ⥤ B) (α : F ⋙ Q ≅ P ⋙ F) : Prop :=
  IsoAlgebra.mapOfNatIso α ⋙ IsoAlgebra.forget Q = IsoAlgebra.forget P ⋙ F ∧
  (∀ K : IsoAlgebra P,
    ((IsoAlgebra.mapOfNatIso α).obj K).carrier = F.obj K.carrier ∧
    ((IsoAlgebra.mapOfNatIso α).obj K).str = α.app K.carrier ≪≫ F.mapIso K.str) ∧
  ∀ (K L : IsoAlgebra P) (u : K ⟶ L),
    ((IsoAlgebra.mapOfNatIso α).map u).hom.f = F.map u.hom.f ∧
    (α.hom.app K.carrier ≫ F.map K.str.hom) ≫ F.map u.hom.f =
      Q.map (F.map u.hom.f) ≫ α.hom.app L.carrier ≫ F.map L.str.hom

/-- The rule for any of the three covariant operations is functorial. This formal
calculation applies to its specified comparison without changing that comparison.
Source: blueprint prop-weil-operations, proof sentence 1, node proof step 6
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: the comparison followed by F(theta) is invertible. Naturality of alpha and
u theta_K = theta_L P(u) give the displayed intertwining equation. The existing
IsoAlgebra transport uses F(u), so identities, composition and forgetting are those
of F. This applies to pullback, ordinary image and compact-support image alike. -/
theorem pod_covariant_field_operation_lift
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} (F : C ⥤ B) (α : F ⋙ Q ≅ P ⋙ F) :
    PodCovariantWeilLiftSpec F α := by
  refine ⟨rfl, fun K ↦ ⟨rfl, IsoAlgebra.mapOfNatIso_obj_str α K⟩, ?_⟩
  intro K L u
  refine ⟨rfl, ?_⟩
  exact ((IsoAlgebra.mapOfNatIso α).map u).hom.h.symm

/-- The tensor lift uses the existing product of fixed pairs and the existing
transport. Source: blueprint prop-weil-operations, proof sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodTensorWeilLiftSpec
    {C : Type a} [Category.{b} C] (P : C ⥤ C) (T : C × C ⥤ C)
    (μ : T ⋙ P ≅ P.prod P ⋙ T) : Prop :=
  (IsoAlgebra.prod ⋙ IsoAlgebra.mapOfNatIso μ) ⋙ IsoAlgebra.forget P =
    ((IsoAlgebra.forget P).prod (IsoAlgebra.forget P)) ⋙ T ∧
  (∀ K L : IsoAlgebra P,
    ((IsoAlgebra.prod ⋙ IsoAlgebra.mapOfNatIso μ).obj (K, L)).str =
      μ.app (K.carrier, L.carrier) ≪≫ T.mapIso (K.str.prod L.str)) ∧
  ∀ (K K' L L' : IsoAlgebra P) (u : K ⟶ K') (v : L ⟶ L'),
    ((IsoAlgebra.prod ⋙ IsoAlgebra.mapOfNatIso μ).map (Prod.mkHom u v)).hom.f =
      T.map (Prod.mkHom u.hom.f v.hom.f)

/-- Retain exactly the original partial internal-Hom domain on underlying objects.
Source: blueprint prop-weil-operations, proof sentence 1, internal-Hom qualification
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podWeilHomPairs {C : Type a} [Category.{b} C] (P : C ⥤ C)
    (J : ObjectProperty (Cᵒᵖ × C)) : ObjectProperty ((IsoAlgebra P)ᵒᵖ × IsoAlgebra P) :=
  fun KL ↦ J (op KL.1.unop.carrier, KL.2.carrier)

/-- Forget structures on a permitted pair, retaining its actual domain witness.
Source: blueprint prop-weil-operations, proof sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podWeilHomPairForget {C : Type a} [Category.{b} C] (P : C ⥤ C)
    (J : ObjectProperty (Cᵒᵖ × C)) :
    (podWeilHomPairs P J).FullSubcategory ⥤ J.FullSubcategory :=
  J.lift ((podWeilHomPairs P J).ι ⋙
    ((IsoAlgebra.forget P).op.prod (IsoAlgebra.forget P))) (fun KL ↦ KL.property)

/-- The Hom structure is H(theta_M inverse,theta_N) after the canonical comparison.
The functor is defined only on the original permitted pairs, and forgetting fixes
its entire object and arrow action. Source: blueprint prop-weil-operations, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodHomWeilLiftSpec
    {C : Type a} [Category.{b} C] (P : C ⥤ C) (J : ObjectProperty (Cᵒᵖ × C))
    (H : J.FullSubcategory ⥤ C)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H) : Prop :=
  ∃ L : (podWeilHomPairs P J).FullSubcategory ⥤ IsoAlgebra P,
    L ⋙ IsoAlgebra.forget P = podWeilHomPairForget P J ⋙ H ∧
    (∀ K : (podWeilHomPairs P J).FullSubcategory,
      HEq (L.obj K).str.hom
        (κ.hom.app ((podWeilHomPairForget P J).obj K) ≫
          H.map (X := (podPairPullback P J J hJ).obj
              ((podWeilHomPairForget P J).obj K))
            (Y := (podWeilHomPairForget P J).obj K)
            (ObjectProperty.homMk
              (Prod.mkHom K.obj.1.unop.str.inv.op K.obj.2.str.hom)))) ∧
    ∀ (K K' : (podWeilHomPairs P J).FullSubcategory) (u : K ⟶ K'),
      HEq (L.map u).hom.f (H.map ((podWeilHomPairForget P J).map u))

/-- The tensor and partial-Hom formulas define functors with the stipulated variances.
The input J can retain any already-proved finite-Tor or site-perfect restriction;
only its preservation by P is used, and no larger Hom domain is asserted.
Source: blueprint prop-weil-operations, sentence 1, node proof steps 7--9
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: tensor uses IsoAlgebra.prod followed by mapOfNatIso. Bifunctoriality,
the two arrow equations and naturality of mu give the tensor arrow equation.
For Hom, send a pair to the permitted underlying pair with structure
(theta_M inverse).op times theta_N; the arrow equation follows by multiplying
the first arrow equation by both inverses. Apply mapOfNatIso to kappa.
The output structure is kappa followed by H(theta_M inverse,theta_N).
Identities and composition are the bifunctor laws, including the reversed
first variable. Forgetting recovers the original tensor and partial Hom. -/
theorem pod_tensor_hom_field_operation_lifts
    {C : Type a} [Category.{b} C] (P : C ⥤ C) (T : C × C ⥤ C)
    (μ : T ⋙ P ≅ P.prod P ⋙ T) (J : ObjectProperty (Cᵒᵖ × C))
    (H : J.FullSubcategory ⥤ C)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H) :
    PodTensorWeilLiftSpec P T μ ∧ PodHomWeilLiftSpec P J H hJ κ := by
  constructor
  · refine ⟨rfl, ?_, fun _ _ _ _ _ _ ↦ rfl⟩
    intro K L
    simp only [Functor.comp_obj, IsoAlgebra.mapOfNatIso_obj_str,
      IsoAlgebra.prod_obj_carrier, IsoAlgebra.prod_obj_str]
  · let R : (IsoAlgebra P)ᵒᵖ × IsoAlgebra P ⥤ IsoAlgebra (P.op.prod P) :=
      (IsoAlgebra.opFunctor.prod (𝟭 (IsoAlgebra P))) ⋙ IsoAlgebra.prod
    let A : (podWeilHomPairs P J).FullSubcategory ⥤
        IsoAlgebra (podPairPullback P J J hJ) :=
      { obj := fun K ↦ IsoAlgebra.mk ((podWeilHomPairForget P J).obj K)
          (J.isoMk (R.obj K.obj).str)
        map := fun u ↦ ObjectProperty.homMk
          { f := (podWeilHomPairForget P J).map u
            h := by
              apply ObjectProperty.hom_ext J
              exact (R.map u.hom).hom.h } }
    refine ⟨A ⋙ IsoAlgebra.mapOfNatIso κ, rfl, ?_, ?_⟩
    · intro K
      rfl
    · intro K K' u
      rfl

/-- The three comparisons and lifts from the supplied operation stage. Its fields
are the actual operation and comparison data on the chosen closed domains in
`def-exchange-projection`; the three equalities identify the same operation on
the two copies of the semilinear square. In particular b and c are the specified
Ex_* and Ex_!, with their original adjunction and compactification normalizations.
Source: blueprint prop-weil-operations, sentence 1, proof steps 4--6
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: pullback comparison is the inverse square compositor. Its direct-image
mate is invertible because horizontal transport is an equivalence and the other
horizontal transport is fully faithful (lem-weil-mate-iso-along-equivalences).
The same argument for the proper factor, followed by the specified open base
change, makes the compactification composite invertible. The rational and
common-stage realizations of lem-pod-weil-frobenius-compact-support-exchange
identify precisely this composite with the canonical compact-support comparison.
Apply the covariant calculation to these three comparisons. -/
theorem pod_supplied_field_operation_lifts
    {X : Type a} {Y : Type b} {B : Type c}
    [Category.{d} X] [Category.{e} Y] [Category.{f} B]
    (S : ExchangeProjectionStage (DX := X) (DY := Y) (DB := B)
      (DX' := X) (DY' := Y) (DB' := B))
    [S.horizontal.IsEquivalence] [S.horizontal'.IsEquivalence]
    [S.compactifyingHorizontal.IsEquivalence]
    (hpull : S.pull' = S.pull) (hpush : S.push' = S.push)
    (hsupport : S.compactSupport' = S.compactSupport) :
    ∃ (α : S.pull ⋙ S.horizontal' ≅ S.horizontal ⋙ S.pull)
      (β : S.push ⋙ S.horizontal ≅ S.horizontal' ⋙ S.push)
      (γ : S.compactSupport ⋙ S.horizontal ≅ S.horizontal' ⋙ S.compactSupport),
      α.hom = S.pullbackComparison.inv ≫
        (Functor.isoWhiskerLeft S.horizontal (eqToIso hpull)).hom ∧
      β.hom = S.exchange ≫
        (Functor.isoWhiskerLeft S.horizontal' (eqToIso hpush)).hom ∧
      γ.hom = S.compactExchange ≫
        (Functor.isoWhiskerLeft S.horizontal' (eqToIso hsupport)).hom ∧
      PodCovariantWeilLiftSpec S.pull α ∧
      PodCovariantWeilLiftSpec S.push β ∧ PodCovariantWeilLiftSpec S.compactSupport γ := by
  have hex : IsIso S.exchange :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful S.adjunction S.adjunction'
      S.horizontal S.horizontal' S.pullbackComparison
  have hproper := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    S.properAdjunction S.properAdjunction' S.horizontal S.compactifyingHorizontal
    S.properPullbackComparison
  have hcompact : IsIso S.compactExchange := by
    unfold ExchangeProjectionStage.compactExchange compactificationExchangeFromData
    infer_instance
  let α := S.pullbackComparison.symm ≪≫
    Functor.isoWhiskerLeft S.horizontal (eqToIso hpull)
  let β := asIso S.exchange ≪≫ Functor.isoWhiskerLeft S.horizontal' (eqToIso hpush)
  let γ := asIso S.compactExchange ≪≫
    Functor.isoWhiskerLeft S.horizontal' (eqToIso hsupport)
  exact ⟨α, β, γ, rfl, rfl, rfl, pod_covariant_field_operation_lift _ α,
    pod_covariant_field_operation_lift _ β, pod_covariant_field_operation_lift _ γ⟩


section CompositionElaboration
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] commonStagePullbackComparison rationalDerivedPullback
  commonStageDerivedPullback Scheme.residueField

attribute [local irreducible] rationalDerivedInternalHom commonStageDerivedInternalHom

-- Retain the category wrappers used by the common-stage operation interface.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] sfIntegralConstructible Linear.homModule
  ObjectProperty.FullSubcategory.category
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

/-- The rational Frobenius square component through the canonical compositors.
Source: blueprint prop-weil-operations, sentence 1, proof step 4
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podRationalSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y) (h : gX ≫ f = f ≫ gY)
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E gX).obj ((rationalDerivedPullback l E f).obj K) ≅
      (rationalDerivedPullback l E f).obj ((rationalDerivedPullback l E gY).obj K) :=
  (pullbackTensorRationalComposition l E f gX K).symm ≪≫
    eqToIso (congrArg (fun m : X ⟶ Y ↦ (rationalDerivedPullback l E m).obj K) h) ≪≫
    pullbackTensorRationalComposition l E gY f K

/-- The same square component in the actual common-stage category, through the
canonical common-stage compositors. Source: blueprint prop-weil-operations, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podCommonSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y) (h : gX ≫ f = f ≫ gY)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω gX).obj ((commonStageDerivedPullback l Ω f).obj K) ≅
      (commonStageDerivedPullback l Ω f).obj ((commonStageDerivedPullback l Ω gY).obj K) :=
  (pullbackTensorCommonComposition l Ω f gX K).symm ≪≫
    eqToIso (congrArg (fun m : X ⟶ Y ↦ (commonStageDerivedPullback l Ω m).obj K) h) ≪≫
    pullbackTensorCommonComposition l Ω gY f K

private theorem pod_map_heq
    {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem pod_rational_composition_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K L : sfRationalConstructibleCategory l E Y} (a : K ⟶ L) :
    (rationalDerivedPullback l E (h ≫ f)).map a ≫
        (pullbackTensorRationalComposition l E f h L).hom =
      (pullbackTensorRationalComposition l E f h K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj M =
        ⟨(constructibleIntegralPullback l E g).obj M.obj⟩ :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfIntegralConstructibleCategory l E W) (b : M ⟶ N)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((rationalDerivedPullback l E g).map (X := ⟨M⟩) (Y := ⟨N⟩)
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] b))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E g).map b) := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 M N b c
  have : (rationalDerivedPullback l E (h ≫ f)).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.1
  have : (rationalDerivedPullback l E f).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : (rationalDerivedPullback l E h).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  have compobj (M) : (rationalDerivedPullback l E h).obj
      ((rationalDerivedPullback l E f).obj M) =
      ⟨(constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj M.obj)⟩ := by
    rw [obj, obj]
  have hc (M) := (pullbackTensorRationalComposition_existsUnique l E f h M).exists.choose_spec
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    have hm := (pod_map_heq (rationalDerivedPullback l E h) (obj f K) (obj f L)
      (hom f K.obj L.obj a c)).trans
        (hom h _ _ ((constructibleIntegralPullback l E f).map a) c)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) L) (compobj L)
      (hom (h ≫ f) K.obj L.obj a c) (hc L)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj L) (hc K) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app L.obj)
        (c ⊗ₜ (constructibleIntegralPullback l E (h ≫ f)).map a) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ (constructibleIntegralPullback l E h).map
          ((constructibleIntegralPullback l E f).map a))
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app K.obj)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun b ↦ c ⊗ₜ b)
      ((pullbackTensorIntegralComposition l E f h).hom.naturality a)
  | add a b ha hb =>
    change (rationalDerivedPullback l E (h ≫ f)).map (a + b : K ⟶ L) ≫ _ =
      _ ≫ (rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E f).map (a + b : K ⟶ L))
    rw [Functor.map_add, Functor.map_add, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add, ha, hb]

attribute [local irreducible] Preadditive.homGroup
  ScalarLocalization.category ScalarLocalization.linear

private theorem pod_composition_representative_naturality
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (G : C ⥤ D) (F : D ⥤ B) (H : C ⥤ B)
    {K N : C} (r : K ⟶ N)
    (eK : H.obj K ≅ F.obj (G.obj K)) (eN : H.obj N ≅ F.obj (G.obj N))
    (nat : H.map r ≫ eN.hom = eK.hom ≫ F.map (G.map r))
    {XK XN : D} {ZK ZN WK WN : B}
    (aK : ZK ≅ H.obj K) (aN : ZN ≅ H.obj N)
    (bK : XK ≅ G.obj K) (bN : XN ≅ G.obj N)
    (dK : WK ≅ F.obj XK) (dN : WN ≅ F.obj XN) :
    (aK.hom ≫ H.map r ≫ aN.inv) ≫
        (aN.hom ≫ eN.hom ≫ F.map bN.inv ≫ dN.inv) =
      (aK.hom ≫ eK.hom ≫ F.map bK.inv ≫ dK.inv) ≫
        (dK.hom ≫ F.map (bK.hom ≫ G.map r ≫ bN.inv) ≫ dN.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.map_inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ aK.hom ≫ t ≫ F.map bN.inv ≫ dN.inv) nat

private theorem pod_ofHom_square
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (P Q R S : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L) (hR : R.stage ≤ L) (hS : S.stage ≤ L)
    (u : P.toStage hP ⟶ Q.toStage hQ) (v : Q.toStage hQ ⟶ S.toStage hS)
    (u' : P.toStage hP ⟶ R.toStage hR) (v' : R.toStage hR ⟶ S.toStage hS)
    (e : u ≫ v = u' ≫ v') :
    GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ u ≫
        GeneralAlgebraicallyClosedCoefficients.ofHom Q S L hQ hS v =
      GeneralAlgebraicallyClosedCoefficients.ofHom P R L hP hR u' ≫
        GeneralAlgebraicallyClosedCoefficients.ofHom R S L hR hS v' := by
  simpa only [GeneralAlgebraicallyClosedCoefficients.ofHom,
    StageSystem.PairCategory.mkHom_comp_mkHom] using
      congrArg (StageSystem.PairCategory.mkHom L hP hS) e

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pod_common_composition_naturality
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K N : generalAlgebraicallyClosedConstructibleCategory l Ω Y} (a : K ⟶ N) :
    (commonStageDerivedPullback l Ω (h ≫ f)).map a ≫
        (pullbackTensorCommonComposition l Ω f h N).hom =
      (pullbackTensorCommonComposition l Ω f h K).hom ≫
        (commonStageDerivedPullback l Ω h).map ((commonStageDerivedPullback l Ω f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)] (M) :
      (commonStageDerivedPullback l Ω g).obj M = commonStagePullbackObject l Ω g M := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L) (hN : N.stage ≤ L)
      (r : M.toStage hM ⟶ N.toStage hN) :
      HEq ((commonStageDerivedPullback l Ω g).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom M N L hM hN r))
        (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStagePullbackObject l Ω g M) (commonStagePullbackObject l Ω g N) L hM hN
          ((commonStagePullbackComparison l Ω g M L hM).hom ≫
            (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              g).map r ≫ (commonStagePullbackComparison l Ω g N L hN).inv)) := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.2 M N L hM hN r
  have compobj (M) : (commonStageDerivedPullback l Ω h).obj
      ((commonStageDerivedPullback l Ω f).obj M) =
      commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M) := by
    rw [obj, obj]
  have hc (M L hM) :=
    (pullbackTensorCommonComposition_existsUnique l Ω f h M).exists.choose_spec L hM
  induction a using StageSystem.PairCategory.hom_induction with
  | h L hK hN r =>
    have hm := (pod_map_heq (commonStageDerivedPullback l Ω h) (obj f K) (obj f N)
      (hom f K N L hK hN r)).trans
        (hom h (commonStagePullbackObject l Ω f K)
          (commonStagePullbackObject l Ω f N) L hK hN _)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) N) (compobj N)
      (hom (h ≫ f) K N L hK hN r) (hc N L hN)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj N) (hc K L hK) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    refine pod_ofHom_square l Ω Z
      (commonStagePullbackObject l Ω (h ≫ f) K)
      (commonStagePullbackObject l Ω (h ≫ f) N)
      (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f K))
      (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f N))
      L hK hN hK hN _ _ _ _ ?_
    have e := @pod_composition_representative_naturality
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z L)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y L)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X L)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Z L)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) h)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (h ≫ f))
      (K.toStage hK) (N.toStage hN)
      r (pullbackTensorRationalComposition l _ f h (K.toStage hK))
      (pullbackTensorRationalComposition l _ f h (N.toStage hN))
      (pod_rational_composition_naturality l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f h
        (K := K.toStage hK) (L := N.toStage hN) r)
      ((commonStagePullbackObject l Ω f K).toStage hK)
      ((commonStagePullbackObject l Ω f N).toStage hN)
      ((commonStagePullbackObject l Ω (h ≫ f) K).toStage hK)
      ((commonStagePullbackObject l Ω (h ≫ f) N).toStage hN)
      ((commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f K)).toStage hK)
      ((commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f N)).toStage hN)
      (commonStagePullbackComparison l Ω (h ≫ f) K L hK)
      (commonStagePullbackComparison l Ω (h ≫ f) N L hN)
      (commonStagePullbackComparison l Ω f K L hK)
      (commonStagePullbackComparison l Ω f N L hN)
      (commonStagePullbackComparison l Ω h (commonStagePullbackObject l Ω f K) L hK)
      (commonStagePullbackComparison l Ω h (commonStagePullbackObject l Ω f N) L hN)
    exact e

private theorem pod_square_app
    {C B : Type*} [Category* C] [Category* B]
    {I : Sort*} (F : I → C ⥤ B) {x y : I} (w : x = y)
    {A D : C ⥤ B} (c₁ : F x ≅ A) (c₂ : F y ≅ D) (K : C) :
    ((c₁.symm ≪≫ eqToIso (congrArg F w) ≪≫ c₂).app K) =
      (c₁.app K).symm ≪≫
        eqToIso (congrArg (fun m ↦ (F m).obj K) w) ≪≫ c₂.app K := by
  cases w
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Actual field pullback has the canonical Frobenius comparison obtained from
its two normalized composition comparisons. The equality of composite scheme maps
is the geometric square equality; both coefficient stages retain that equality.
Source: blueprint prop-weil-operations, sentence 1, node proof step 4
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: integralPullbackComposition gives the comparisons through L(f g_X)* and
L(g_Y f)*. The Cartesian Frobenius square identifies these maps. Invert the first
comparison and follow by the second. Naturality holds integrally, hence on raw
localized Hom groups. Pullback-identities scalar compatibility makes their common
finite-stage classes natural and independent of the representative. The covariant
calculation then gives both fixed-pair functors with the displayed structure. -/
theorem pod_actual_pullback_field_lifts
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (f : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left)
    (hf : f = ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).map f₀).left)
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    (fun [_hx : ∀ x : (D.geometricFiber X₀).left,
        Invertible (l : (D.geometricFiber X₀).left.residueField x)]
      [_hy : ∀ y : (D.geometricFiber Y₀).left,
        Invertible (l : (D.geometricFiber Y₀).left.residueField y)] ↦
      ∃ (h : f ≫ (D.geometricFrobenius Y₀).hom =
          (D.geometricFrobenius X₀).hom ≫ f)
        (α : rationalDerivedPullback l E f ⋙
              sfWeilFrobeniusPullback D l hl X₀ E ≅
          sfWeilFrobeniusPullback D l hl Y₀ E ⋙ rationalDerivedPullback l E f)
        (β : commonStageDerivedPullback l Ω f ⋙
              sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
          sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ⋙ commonStageDerivedPullback l Ω f),
        (∀ K, HEq (α.app K) (podRationalSquarePullbackComponent l E f
          (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom h.symm K)) ∧
        (∀ K, HEq (β.app K) (podCommonSquarePullbackComponent l Ω f
          (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom h.symm K)) ∧
        PodCovariantWeilLiftSpec (rationalDerivedPullback l E f) α ∧
        PodCovariantWeilLiftSpec (commonStageDerivedPullback l Ω f) β)
      (_hx := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
      (_hy := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y) := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  dsimp only [sfWeilFrobeniusPullback, sfCommonStageWeilFrobeniusPullback]
  have w : (D.geometricFrobenius X₀).hom ≫ f =
      f ≫ (D.geometricFrobenius Y₀).hom := by
    subst f
    exact (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1
  let cr (V W Z : Scheme.{u}) (g : V ⟶ W) (h : Z ⟶ V)
      [∀ x : V, Invertible (l : V.residueField x)]
      [∀ y : W, Invertible (l : W.residueField y)]
      [∀ z : Z, Invertible (l : Z.residueField z)] :
      rationalDerivedPullback l E (h ≫ g) ≅
        rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E h :=
    NatIso.ofComponents (pullbackTensorRationalComposition l E g h)
      (fun a ↦ pod_rational_composition_naturality l E g h a)
  let cc (V W Z : Scheme.{u}) (g : V ⟶ W) (h : Z ⟶ V)
      [∀ x : V, Invertible (l : V.residueField x)]
      [∀ y : W, Invertible (l : W.residueField y)]
      [∀ z : Z, Invertible (l : Z.residueField z)] :
      commonStageDerivedPullback l Ω (h ≫ g) ≅
        commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω h :=
    NatIso.ofComponents (pullbackTensorCommonComposition l Ω g h)
      (fun a ↦ pod_common_composition_naturality l Ω g h a)
  let α := (cr _ _ _ f (D.geometricFrobenius X₀).hom).symm ≪≫
    eqToIso (congrArg (fun m : _ ⟶ _ ↦ rationalDerivedPullback l E m) w) ≪≫
      cr _ _ _ (D.geometricFrobenius Y₀).hom f
  let β := (cc _ _ _ f (D.geometricFrobenius X₀).hom).symm ≪≫
    eqToIso (congrArg (fun m : _ ⟶ _ ↦ commonStageDerivedPullback l Ω m) w) ≪≫
      cc _ _ _ (D.geometricFrobenius Y₀).hom f
  refine ⟨w.symm, α, β, ?_, ?_, pod_covariant_field_operation_lift _ α,
    pod_covariant_field_operation_lift _ β⟩
  · intro K
    exact heq_of_eq (pod_square_app
      (fun m : _ ⟶ _ ↦ rationalDerivedPullback l E m) w
      (cr _ _ _ f (D.geometricFrobenius X₀).hom)
      (cr _ _ _ (D.geometricFrobenius Y₀).hom f) K)
  · intro K
    exact heq_of_eq (pod_square_app
      (fun m : _ ⟶ _ ↦ commonStageDerivedPullback l Ω m) w
      (cc _ _ _ f (D.geometricFrobenius X₀).hom)
      (cc _ _ _ (D.geometricFrobenius Y₀).hom f) K)


end CompositionElaboration

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]

/-- Integral and rational Frobenius transport, using the existing prime-invertibility
data, canonical inverse-image realization, and the actual inverse scheme map.
Source: blueprint prop-weil-operations, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodRationalFrobeniusTransportSpec
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  (∃ ε : constructibleIntegralPullback l E (D.geometricFrobenius T₀).hom ⋙
      constructibleIntegralPullback l E (D.geometricFrobenius T₀).inv ≅ 𝟭 _,
    ∀ K : sfIntegralConstructibleCategory l E (D.geometricFiber T₀).left,
      HEq ((sfIntegralConstructible l E (D.geometricFiber T₀).left).ι.map (ε.hom.app K))
        (pullbackIdentityEpsilon l E (D.geometricFrobenius T₀).hom K).hom) ∧
  Nonempty (constructibleIntegralPullback l E (D.geometricFrobenius T₀).inv ⋙
    constructibleIntegralPullback l E (D.geometricFrobenius T₀).hom ≅ 𝟭 _) ∧
  (∃ h : ∀ K : DerivedCategory (scalarReductionSource l E (D.geometricFiber T₀).left),
      sfIntegralConstructible l E (D.geometricFiber T₀).left K →
        sfIntegralConstructible l E (D.geometricFiber T₀).left
          ((isomorphismIntegralTermwiseInverseImage l E
            (D.geometricFrobenius T₀).hom).obj K),
    Nonempty (constructibleIntegralPullback l E (D.geometricFrobenius T₀).hom ≅
      (sfIntegralConstructible l E (D.geometricFiber T₀).left).lift
        ((sfIntegralConstructible l E (D.geometricFiber T₀).left).ι ⋙
          isomorphismIntegralTermwiseInverseImage l E (D.geometricFrobenius T₀).hom)
        (fun K ↦ h K.obj K.property))) ∧
  (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).hom).Additive ∧
  PreservesFiniteLimits
    (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).hom) ∧
  PreservesFiniteColimits
    (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).hom) ∧
  (podCompletedModuleInverseImage l E (D.geometricFrobenius T₀).hom).IsEquivalence ∧
  (sfWeilFrobeniusPullback D l hl T₀ E).IsEquivalence ∧
  (∃ (δ : constructibleIntegralPullback l E (D.geometricFrobenius T₀).hom ⋙
        constructibleIntegralPullback l E (D.geometricFrobenius T₀).inv ≅ 𝟭 _)
      (ε : sfWeilFrobeniusPullback D l hl T₀ E ⋙
        rationalDerivedPullback l E (D.geometricFrobenius T₀).inv ≅ 𝟭 _),
    (∀ K, HEq ((sfIntegralConstructible l E (D.geometricFiber T₀).left).ι.map
        (δ.hom.app K)) (pullbackIdentityEpsilon l E (D.geometricFrobenius T₀).hom K).hom) ∧
    ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber T₀).left,
      HEq (ε.hom.app K)
        ((sfRationalConstructibleLocalization l E (D.geometricFiber T₀).left).map
          (δ.hom.app K.obj))) ∧
  Nonempty (rationalDerivedPullback l E (D.geometricFrobenius T₀).inv ⋙
    sfWeilFrobeniusPullback D l hl T₀ E ≅ 𝟭 _) ∧
  ∃ s : (sfWeilFrobeniusPullback D l hl T₀ E).CommShift ℤ,
    (fun [_s : (sfWeilFrobeniusPullback D l hl T₀ E).CommShift ℤ] ↦
      (sfWeilFrobeniusPullback D l hl T₀ E).IsTriangulated) (_s := s)


/-- Both coefficient stages use the actual inverse scheme map, and their underlying
pullbacks are exact equivalences. Tensor and Hom comparisons below are fixed to
the recorded canonical transport maps, rather than arbitrary isomorphisms.
Source: blueprint prop-weil-operations, sentence 1, node proof steps 2--3 and 7--8
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodFieldOperationTransportSpec
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  PodRationalFrobeniusTransportSpec D l hl T₀ E ∧
  (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsEquivalence ∧
  (∃ ε : sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ⋙
      commonStageDerivedPullback l Ω (D.geometricFrobenius T₀).inv ≅ 𝟭 _,
    ∀ A : AlgebraicallyClosedCoefficients.Index l Ω,
      ∃ δ : sfWeilFrobeniusPullback D l hl T₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) ⋙
        rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          (D.geometricFrobenius T₀).inv ≅ 𝟭 _,
        ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber T₀).left A,
          HEq (ε.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion A).obj K))
            ((GeneralAlgebraicallyClosedCoefficients.inclusion A).map (δ.hom.app K))) ∧
  Nonempty (commonStageDerivedPullback l Ω (D.geometricFrobenius T₀).inv ⋙
    sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ≅ 𝟭 _) ∧
  (∃ s : (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).CommShift ℤ,
    (fun [_s : (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).CommShift ℤ] ↦
      (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsTriangulated) (_s := s)) ∧
  (∃ μ : rationalDerivedTensor l E (D.geometricFiber T₀).left ⋙
        sfWeilFrobeniusPullback D l hl T₀ E ≅
      (sfWeilFrobeniusPullback D l hl T₀ E).prod
        (sfWeilFrobeniusPullback D l hl T₀ E) ⋙
          rationalDerivedTensor l E (D.geometricFiber T₀).left,
    (∀ K L, μ.app (K, L) =
      canonicalRationalPullbackTensor l E (D.geometricFrobenius T₀).hom K L) ∧
    PodTensorWeilLiftSpec (sfWeilFrobeniusPullback D l hl T₀ E)
      (rationalDerivedTensor l E (D.geometricFiber T₀).left) μ) ∧
  (∃ μ : commonStageDerivedTensor l Ω (D.geometricFiber T₀).left ⋙
        sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ≅
      (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).prod
        (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω) ⋙
          commonStageDerivedTensor l Ω (D.geometricFiber T₀).left,
    (∀ K L, μ.app (K, L) =
      canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius T₀).hom K L) ∧
    PodTensorWeilLiftSpec (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
      (commonStageDerivedTensor l Ω (D.geometricFiber T₀).left) μ) ∧
  (∃ κ : rationalDerivedInternalHom l E (D.geometricFiber T₀).left ⋙
        sfWeilFrobeniusPullback D l hl T₀ E ≅
      podPairPullback (sfWeilFrobeniusPullback D l hl T₀ E)
        (constructibleRationalHomPairs l E (D.geometricFiber T₀).left)
        (constructibleRationalHomPairs l E (D.geometricFiber T₀).left)
        (podRationalPairs_pullback l E (D.geometricFrobenius T₀).hom) ⋙
          rationalDerivedInternalHom l E (D.geometricFiber T₀).left,
    (∀ K, κ.hom.app K = podRationalHomComparison l E (D.geometricFrobenius T₀).hom K) ∧
    PodHomWeilLiftSpec (sfWeilFrobeniusPullback D l hl T₀ E)
      (constructibleRationalHomPairs l E (D.geometricFiber T₀).left)
      (rationalDerivedInternalHom l E (D.geometricFiber T₀).left)
      (podRationalPairs_pullback l E (D.geometricFrobenius T₀).hom) κ) ∧
  ∃ κ : commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left ⋙
        sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω ≅
      podPairPullback (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
        (commonStageHomPairs l Ω (D.geometricFiber T₀).left)
        (commonStageHomPairs l Ω (D.geometricFiber T₀).left)
        (podCommonPairs_pullback l Ω (D.geometricFrobenius T₀).hom) ⋙
          commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left,
    (∀ K, κ.hom.app K = podCommonHomComparison l Ω (D.geometricFrobenius T₀).hom K) ∧
    PodHomWeilLiftSpec (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
      (commonStageHomPairs l Ω (D.geometricFiber T₀).left)
      (commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left)
      (podCommonPairs_pullback l Ω (D.geometricFrobenius T₀).hom) κ

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence commonStageTensorComparison
  operationStageTransitionIso commonStageDerivedTensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pod_field_transport
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    PodFieldOperationTransportSpec D l hl T₀ E Ω := by
  let i := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  let : ∀ x : (D.geometricFiber T₀).left,
      Invertible (l : (D.geometricFiber T₀).left.residueField x) := i
  let : (D.geometricFiber T₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber T₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (LocallyOfFiniteType
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (QuasiCompact
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : IsIso (D.geometricFrobenius T₀).hom := (D.geometricFrobenius T₀).isIso_hom
  obtain ⟨iX, iY, H⟩ := isomorphismFieldTransport D l hl Ω
    (D.geometricFrobenius T₀).hom
  have hiX : iX = i := Subsingleton.elim _ _
  have hiY : iY = i := Subsingleton.elim _ _
  cases hiX
  cases hiY
  obtain ⟨hX, hY, hE, _, S, R, _, ⟨U⟩, ⟨V⟩⟩ := H
  obtain ⟨A⟩ := (hE E).1
  obtain ⟨B⟩ := (hE E).2
  have ht := isomorphismIntegralDerivedPullback_termwise l E
    (D.geometricFrobenius T₀).hom
  obtain ⟨h, ht, _⟩ := ht
  have hrat : PodRationalFrobeniusTransportSpec D l hl T₀ E := by
    unfold PodRationalFrobeniusTransportSpec
    dsimp only [sfWeilFrobeniusPullback]
    rw [← IsIso.Iso.inv_hom (D.geometricFrobenius T₀)]
    refine ⟨⟨A.epsilon, ?_⟩, ?_, ⟨h, ht⟩, inferInstance, inferInstance,
      inferInstance, (podCompletedInverseImage_equivalence l E
        (D.geometricFrobenius T₀).hom).1, A.rationalEquivalence,
      ⟨A.epsilon, A.rationalEpsilon, ?_, A.rational_epsilon_formula⟩, ?_,
      ⟨A.rationalShift, A.rationalExact⟩⟩
    · intro K
      exact A.epsilon_formula K
    · simpa only [IsIso.inv_inv, IsIso.Iso.inv_hom] using Nonempty.intro B.epsilon
    · intro K
      exact A.epsilon_formula K
    · simpa only [IsIso.inv_inv, IsIso.Iso.inv_hom, sfWeilFrobeniusPullback] using
        Nonempty.intro B.rationalEpsilon
  have tensor := derivedPullbackTensorIso l E (D.geometricFrobenius T₀).hom 0 Ω
  obtain ⟨μ, hμ⟩ := tensor.2.2.2.2.2.2.1
  obtain ⟨ν, hν⟩ := tensor.2.2.2.2.2.2.2.1
  have homs := derivedAutomorphismHomEvaluation l E (D.geometricFrobenius T₀).hom 0 Ω
  obtain ⟨κ, hκ⟩ := homs.2.2.1
  obtain ⟨ρ, hρ⟩ := homs.2.2.2.1
  unfold PodFieldOperationTransportSpec
  dsimp only [sfWeilFrobeniusPullback, sfCommonStageWeilFrobeniusPullback]
  rw [← IsIso.Iso.inv_hom (D.geometricFrobenius T₀)]
  refine ⟨hrat, U.equivalence, ⟨U.epsilon, ?_⟩, ?_, ⟨U.shift, U.exact⟩,
    ⟨μ, hμ, ?_⟩, ⟨ν, hν, ?_⟩, ⟨κ, hκ, ?_⟩, ⟨ρ, hρ, ?_⟩⟩
  · intro L
    refine ⟨(S L).rationalEpsilon, ?_⟩
    intro K
    exact U.epsilon_formula ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)
  · simpa only [IsIso.inv_inv, IsIso.Iso.inv_hom,
      sfCommonStageWeilFrobeniusPullback] using Nonempty.intro V.epsilon
  · exact (pod_tensor_hom_field_operation_lifts _ _ μ _ _ _ κ).1
  · exact (pod_tensor_hom_field_operation_lifts _ _ ν _ _ _ ρ).1
  · exact (pod_tensor_hom_field_operation_lifts _ _ μ _ _ _ κ).2
  · exact (pod_tensor_hom_field_operation_lifts _ _ ν _ _ _ ρ).2

/-- Semilinear Frobenius geometry, exact field transport, and the canonical tensor
and internal-Hom lifts on both models. The covariant lifts, including the specified
Ex_* and Ex_!, are `pod_supplied_field_operation_lifts`; their explicit object and
arrow calculation is `pod_covariant_field_operation_lift`.
Source: blueprint main-20261015, prop-weil-operations.proof.md, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts).

Proof (the original nine steps, with existing field-transport records reused):
1. Apply lem-weil-frobenius-square-cartesian to the geometric scalar extension.
The upper structure map is g_T followed by a_T. Commutativity and f being over k
make the left vertical arrow a map between precisely those restructured corners;
no k-linearity of g_T is asserted, including when a model is nonseparated.
2. The exact inverse-image equivalence on completed modules identifies integral
pullback with termwise transport (lem-weil-proetale-isomorphism-inverse-image and
lem-weil-isomorphism-derived-pullback). Compose lambda for g and its inverse
with the inverse-image counit to obtain the normalized epsilon and its reverse.
3. Localize the integral inverse equations linearly on Hom tensor E. At common
stages represent an arrow over one finite field. Scalar compatibility of the
inverse identities (lem-pod-pullback-identities-scalar-extension) and the specified
operation scalar comparisons turn its naturality square into that finite-stage
square. Identity extensions and tower cocycles preserve its class. Exactness
comes from the exact module transport, integral triangles and common-stage triangles.
4. For pullback compose the inverse compositor for (g_X,f) with that for (f,g_Y).
Integral composition is lem-pod-integral-pullback-composition; its scalar equation
descends to rational and common stages, with the same comparison on every arrow.
5. The mate of its inverse is exactly Ex_* of def-exchange-projection. Horizontal
equivalences make it invertible by lem-weil-mate-iso-along-equivalences. For Ex_!,
the proper mate is invertible by the same argument; compose it with the supplied
open comparison and the compactification identifications on the preserved domain.
6. The covariant calculation is pod_covariant_field_operation_lift. Applying it
to those comparisons gives pod_supplied_field_operation_lifts, with the actual
supplied-domain units, counits, compactification and coefficient normalizations.
7. The canonical tensor comparison is lem-pur-derived-pullback-tensor-iso.
Tensoring the two structure maps after it gives the tensor lift and its arrow law.
8. Lem-pod-derived-automorphism-hom-evaluation supplies the evaluation-defined Hom
comparison, natural on exactly the permitted pairs. Apply the inverse structure
in the first variable and the forward structure in the second. The inverse
intertwining equation and comparison naturality give the Hom arrow law.
9. The forgetful equalities retain every original object and arrow. Finite-Tor
field categories equal the bounded constructible categories by definition.
Any previously imposed site-perfect first-variable subdomain remains a restriction
of the same permitted-pair functor. No new constructibility or triangulation
of fixed pairs is inferred. -/
theorem semilinearFieldOperationLifts
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    IsPullback (D.geometricFrobenius X₀).hom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      (D.geometricFrobenius Y₀).hom ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        (D.geometricFrobenius Y₀).hom ≫ (D.geometricFiber Y₀).hom =
      (D.geometricFrobenius X₀).hom ≫ (D.geometricFiber X₀).hom ∧
    PodFieldOperationTransportSpec D l hl X₀ E Ω ∧
    PodFieldOperationTransportSpec D l hl Y₀ E Ω := by
  have hgeom := D.frobenius_square_cartesian X₀ Y₀ f₀
  refine ⟨hgeom.2.2.2.2.2.1, ?_, pod_field_transport D l hl X₀ E Ω,
    pod_field_transport D l hl Y₀ E Ω⟩
  have hc : (D.geometricFrobenius X₀).hom ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        (D.geometricFrobenius Y₀).hom := hgeom.2.2.2.2.1
  rw [← Category.assoc, ← hc, Category.assoc]
  congr 1
  exact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap D.k₀ D.k)))).map f₀).w

end WeilConjectures
