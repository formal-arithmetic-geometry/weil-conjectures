/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.PoincareDuality.PullbackIdentitiesScalarExtension
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.CategoryTheory.CofilteredIsoComparison
public import WeilConjectures.Compactification.Cofiltered
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed

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

/-- Pullback on the original permitted pairs, with their original witnesses.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podHomPairPullback {C : Type a} [Category.{b} C] (P : C ⥤ C)
    (J : ObjectProperty (Cᵒᵖ × C))
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj)) :
    J.FullSubcategory ⥤ J.FullSubcategory :=
  J.lift (J.ι ⋙ P.op.prod P) hJ

/-- Restrict the given comparison to the original preserved input and output domains.
This uses precisely the supplied preservation proofs and the full-subcategory inclusion.
Source: lem-fix-weil-operations.proof.md, paragraph 1, stated operation domains
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podRestrictedCovariantComparison
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} (F : C ⥤ B) (α : F ⋙ Q ≅ P ⋙ F)
    (I : ObjectProperty C) (J : ObjectProperty B)
    (hP : ∀ K : I.FullSubcategory, I (P.obj K.obj))
    (hQ : ∀ K : J.FullSubcategory, J (Q.obj K.obj))
    (hF : ∀ K : I.FullSubcategory, J (F.obj K.obj)) :
    J.lift (I.ι ⋙ F) hF ⋙ J.lift (J.ι ⋙ Q) hQ ≅
      I.lift (I.ι ⋙ P) hP ⋙ J.lift (I.ι ⋙ F) hF :=
  NatIso.ofComponents (fun K ↦ J.isoMk (α.app K.obj))
    (fun t ↦ by
      apply ObjectProperty.hom_ext
      exact α.hom.naturality t.hom)

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
    (κ : H ⋙ P ≅ podHomPairPullback P J hJ ⋙ H) : Prop :=
  ∃ L : (podWeilHomPairs P J).FullSubcategory ⥤ IsoAlgebra P,
    L ⋙ IsoAlgebra.forget P = podWeilHomPairForget P J ⋙ H ∧
    (∀ K : (podWeilHomPairs P J).FullSubcategory,
      HEq (L.obj K).str.hom
        (κ.hom.app ((podWeilHomPairForget P J).obj K) ≫
          H.map (X := (podHomPairPullback P J hJ).obj
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
    (κ : H ⋙ P ≅ podHomPairPullback P J hJ ⋙ H) :
    PodTensorWeilLiftSpec P T μ ∧ PodHomWeilLiftSpec P J H hJ κ := by
  constructor
  · refine ⟨rfl, ?_, fun _ _ _ _ _ _ ↦ rfl⟩
    intro K L
    simp only [Functor.comp_obj, IsoAlgebra.mapOfNatIso_obj_str,
      IsoAlgebra.prod_obj_carrier, IsoAlgebra.prod_obj_str]
  · let R : (IsoAlgebra P)ᵒᵖ × IsoAlgebra P ⥤ IsoAlgebra (P.op.prod P) :=
      (IsoAlgebra.opFunctor.prod (𝟭 (IsoAlgebra P))) ⋙ IsoAlgebra.prod
    let A : (podWeilHomPairs P J).FullSubcategory ⥤
        IsoAlgebra (podHomPairPullback P J hJ) :=
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

/-- The evaluation-defined internal-Hom comparison, natural in both variables.
Source: lem-fix-weil-operations.proof.md, paragraph 1; the monoidal equivalence
comparison of lem-pur-monoidal-equivalence-hom-comparison
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podClosedHomComparison :
    Functor.uncurry.obj MonoidalClosed.internalHom ⋙ P ≅
      P.op.prod P ⋙ Functor.uncurry.obj MonoidalClosed.internalHom :=
  NatIso.ofComponents (fun KL ↦ Functor.Monoidal.ihomObjIso P KL.1.unop KL.2)
    (fun {KL KL'} t ↦ by
      change P.map ((MonoidalClosed.pre t.1.unop).app KL.2 ≫
          (ihom KL'.1.unop).map t.2) ≫
            (Functor.LaxMonoidal.ihomComparison P KL'.1.unop).natTrans.app KL'.2 =
        (Functor.LaxMonoidal.ihomComparison P KL.1.unop).natTrans.app KL.2 ≫
          (MonoidalClosed.pre (P.map t.1.unop)).app (P.obj KL.2) ≫
            (ihom (P.obj KL'.1.unop)).map (P.map t.2)
      have hn := (Functor.LaxMonoidal.ihomComparison P KL'.1.unop).natTrans.naturality t.2
      dsimp only [Functor.comp_map] at hn
      rw [P.map_comp, Category.assoc, hn]
      rw [← Category.assoc,
        Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app, Category.assoc])

/-- The canonical tensor comparison, with its two-variable naturality.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podClosedTensorComparison :
    Functor.uncurry.obj (curriedTensor C) ⋙ P ≅
      P.prod P ⋙ Functor.uncurry.obj (curriedTensor C) :=
  NatIso.ofComponents (fun KL ↦ (Functor.Monoidal.μIso P KL.1 KL.2).symm)
    (fun t ↦ by
      simp [Functor.uncurry, curriedTensor])

/-- Ordinary bounded-constructible pullback for any scheme map, including semilinear maps.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podConstructiblePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.BoundedConstructible (condensedRingObj Λ Y) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ X) :=
  (ProEtale.boundedConstructible _).lift
    ((ProEtale.boundedConstructible _).ι ⋙ P Λ f)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f K.obj K.property)

/-- The restricted pullback has exactly the ambient pullback after inclusion.
Source: lem-fix-weil-operations.proof.md, paragraph 1, preserved constructible domains
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podConstructiblePullbackInclusion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    podConstructiblePullback Λ f ⋙ (boundedConstructible (condensedRingObj Λ X)).ι ≅
      (boundedConstructible (condensedRingObj Λ Y)).ι ⋙ P Λ f :=
  Iso.refl _

/-- The actual inverse scheme map induces the inverse equivalence on bounded
constructible complexes, with no field-linearity or absolute separatedness assumption.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podConstructibleEquivalence (T : Scheme.{u}) (g : T ≅ T) :
    ProEtale.BoundedConstructible (condensedRingObj Λ T) ≌
      ProEtale.BoundedConstructible (condensedRingObj Λ T) :=
  CategoryTheory.Equivalence.mk (podConstructiblePullback Λ g.hom)
    (podConstructiblePullback Λ g.inv)
    (NatIso.ofComponents
      (fun K ↦ (ProEtale.boundedConstructible _).isoMk
        (((leftDerivedUpperStarComp Λ g.inv g.hom).symm ≪≫
          eqToIso (congrArg (P Λ) g.inv_hom_id) ≪≫ leftDerivedUpperStarId Λ T).symm.app
            K.obj))
      (fun t ↦ by
        apply ObjectProperty.hom_ext
        exact (((leftDerivedUpperStarComp Λ g.inv g.hom).symm ≪≫
          eqToIso (congrArg (P Λ) g.inv_hom_id) ≪≫ leftDerivedUpperStarId Λ T).symm.hom.naturality
            t.hom)))
    (NatIso.ofComponents
      (fun K ↦ (ProEtale.boundedConstructible _).isoMk
        (((leftDerivedUpperStarComp Λ g.hom g.inv).symm ≪≫
          eqToIso (congrArg (P Λ) g.hom_inv_id) ≪≫ leftDerivedUpperStarId Λ T).app K.obj))
      (fun t ↦ by
        apply ObjectProperty.hom_ext
        exact (((leftDerivedUpperStarComp Λ g.hom g.inv).symm ≪≫
          eqToIso (congrArg (P Λ) g.hom_inv_id) ≪≫ leftDerivedUpperStarId Λ T).hom.naturality
            t.hom)))

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

attribute [local irreducible] Preadditive.homGroup
  ScalarLocalization.category ScalarLocalization.linear

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
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

/-- Exact transport by a scheme automorphism on the ordinary condensed module category.
Both inverse equations use the actual inverse scheme map and the native compositors.
Tensor and Hom use the canonical monoidal and evaluation comparisons.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodFieldOperationTransportSpec (T : Scheme.{u}) (g : T ≅ T) : Prop :=
  (P Λ g.hom).IsEquivalence ∧
  (podConstructiblePullback Λ g.hom).IsEquivalence ∧
  Nonempty (P Λ g.hom ⋙ P Λ g.inv ≅ 𝟭 (D Λ T)) ∧
  Nonempty (P Λ g.inv ⋙ P Λ g.hom ≅ 𝟭 (D Λ T)) ∧
  Nonempty (P Λ g.hom ≅ (upperStar Λ g.hom).mapDerivedCategory) ∧
  (P Λ g.hom).IsTriangulated ∧
  PodTensorWeilLiftSpec (P Λ g.hom) (Functor.uncurry.obj (curriedTensor (D Λ T)))
    (podClosedTensorComparison (P Λ g.hom)) ∧
  ∀ (J : ObjectProperty ((D Λ T)ᵒᵖ × D Λ T))
    (hJ : ∀ K : J.FullSubcategory, J (((P Λ g.hom).op.prod (P Λ g.hom)).obj K.obj)),
    PodHomWeilLiftSpec (P Λ g.hom) J
      (J.ι ⋙ Functor.uncurry.obj MonoidalClosed.internalHom) hJ
      (Functor.isoWhiskerLeft J.ι (podClosedHomComparison (P Λ g.hom)))

/-- Scheme-isomorphism transport preserves the explicit tensor and Hom formulas.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: the native exact inverse image is an equivalence and its total derived functor
is termwise transport. Compose the inverse compositor with the identity comparison
for each inverse equation. Apply the general pair calculation to the canonical
monoidal tensorator and the evaluation transpose; restrict the latter to J. -/
theorem pod_field_transport (T : Scheme.{u}) (g : T ≅ T) :
    PodFieldOperationTransportSpec Λ T g := by
  refine ⟨inferInstance, (podConstructibleEquivalence Λ T g).isEquivalence_functor, ?_, ?_,
    ⟨leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom⟩, inferInstance, ?_, ?_⟩
  · exact ⟨(leftDerivedUpperStarComp Λ g.inv g.hom).symm ≪≫
      eqToIso (congrArg (P Λ) g.inv_hom_id) ≪≫ leftDerivedUpperStarId Λ T⟩
  · exact ⟨(leftDerivedUpperStarComp Λ g.hom g.inv).symm ≪≫
      eqToIso (congrArg (P Λ) g.hom_inv_id) ≪≫ leftDerivedUpperStarId Λ T⟩
  · refine ⟨rfl, ?_, fun _ _ _ _ _ _ ↦ rfl⟩
    intro K L
    simp only [Functor.comp_obj, IsoAlgebra.mapOfNatIso_obj_str,
      IsoAlgebra.prod_obj_carrier, IsoAlgebra.prod_obj_str]
  · intro J hJ
    exact (pod_tensor_hom_field_operation_lifts (P Λ g.hom) _
      (podClosedTensorComparison (P Λ g.hom)) J
      (J.ι ⋙ Functor.uncurry.obj MonoidalClosed.internalHom) hJ
      (Functor.isoWhiskerLeft J.ι (podClosedHomComparison (P Λ g.hom)))).2

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence commonStageTensorComparison
  operationStageTransitionIso commonStageDerivedTensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native pullback and ordinary direct-image comparisons lift to Weil pairs.
The comparison for direct image is the actual adjunction mate Ex_*.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: pullback uses the inverse native square compositor. Pullback by both horizontal
scheme isomorphisms is an equivalence, so the mate itself is invertible. Apply the
explicit covariant calculation to the two canonical comparisons. -/
theorem pod_actual_pullback_field_lifts
    {X Y : Scheme.{u}} (gX : X ≅ X) (gY : Y ≅ Y) (f : X ⟶ Y)
    (w : gX.hom ≫ f = f ≫ gY.hom) :
    PodCovariantWeilLiftSpec (P Λ f) (pullbackSquareComparison Λ (CommSq.mk w)).symm ∧
    ∃ β : R Λ f ⋙ P Λ gY.hom ≅ P Λ gX.hom ⋙ R Λ f,
      β.hom = baseChangeMap Λ (CommSq.mk w) ∧
      PodCovariantWeilLiftSpec (R Λ f) β := by
  have : IsIso (baseChangeMap Λ (CommSq.mk w)) :=
    Adjunction.isIso_exchangeRight_of_isEquivalence
      (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f)
      (pullbackSquareComparison Λ (CommSq.mk w))
  exact ⟨pod_covariant_field_operation_lift _ _,
    asIso (baseChangeMap Λ (CommSq.mk w)), rfl, pod_covariant_field_operation_lift _ _⟩

/-- The native compact-support lift uses the stipulated proper/open exchange, for every
supplied automorphism diagram of the chosen compactification.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: the proper mate and the specified open comparison are invertible. Their
compactification composite is therefore invertible. Apply the covariant arrow
calculation to that same composite, without selecting a different comparison. -/
theorem pod_supplied_field_operation_lifts
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (gX : X ≅ X) (gY : Y ≅ Y) (s : Square c c gX.hom gY.hom)
    [IsIso s.middle] (w : gX.hom ≫ f = f ≫ gY.hom) :
    ∃ γ : F Λ c ⋙ P Λ gY.hom ≅ P Λ gX.hom ⋙ F Λ c,
      γ.hom = squareExchange Λ s ∧ PodCovariantWeilLiftSpec (F Λ c) γ := by
  have : IsIso (squareExchange Λ s) := (square_isIso Λ s (CommSq.mk w)).2
  exact ⟨asIso (squareExchange Λ s), rfl, pod_covariant_field_operation_lift _ _⟩

/-- Transport a compactification along both actual scheme automorphisms.
Its middle scheme is unchanged; its open and proper maps change explicitly.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podTransportCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (gX : X ≅ X) (gY : Y ≅ Y)
    (w : gX.hom ≫ f = f ≫ gY.hom) : Compactification f where
  Z := c.Z
  g := c.g ≫ gY.inv
  i := gX.hom ≫ c.i
  comm := by
    calc
      f = (f ≫ gY.hom) ≫ gY.inv := by simp
      _ = (gX.hom ≫ f) ≫ gY.inv := by rw [w]
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun h : X ⟶ Y ↦ (gX.hom ≫ h) ≫ gY.inv) c.comm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The transported compactification has a canonical isomorphism square to the original.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podTransportCompactificationSquare {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (gX : X ≅ X) (gY : Y ≅ Y)
    (w : gX.hom ≫ f = f ≫ gY.hom) :
    Square c (podTransportCompactification c gX gY w) gX.hom gY.hom where
  middle := 𝟙 c.Z
  openSquare := by
    change IsPullback gX.hom (gX.hom ≫ c.i) c.i (𝟙 c.Z)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  properSquare := ⟨by simp [podTransportCompactification]⟩

/-- Return the proper/open exchange to the chosen compactification using the
specified constructible common-refinement comparison. No automorphism of the
chosen middle scheme is assumed.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
@[irreducible] def podReindexedCompactComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (gX : X ≅ X) (gY : Y ≅ Y)
    (w : gX.hom ≫ f = f ≫ gY.hom)
    (τ : (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        F Λ (podTransportCompactification c gX gY w) ≅
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c) :
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c) ⋙ P Λ gY.hom ≅
      podConstructiblePullback Λ gX.hom ⋙
        ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c) := by
  let s := podTransportCompactificationSquare c gX gY w
  have : IsIso s.middle := by
    change IsIso (𝟙 c.Z)
    infer_instance
  have : IsIso (squareExchange Λ s) := (square_isIso Λ s (CommSq.mk w)).2
  let I := (boundedConstructible (condensedRingObj Λ X)).ι
  let P₀ := podConstructiblePullback Λ gX.hom
  let c' := podTransportCompactification c gX gY w
  exact Functor.associator I (F Λ c) (P Λ gY.hom) ≪≫
    Functor.isoWhiskerLeft I (asIso (squareExchange Λ s)) ≪≫
    (Functor.associator I (P Λ gX.hom) (F Λ c')).symm ≪≫
    Functor.isoWhiskerRight (podConstructiblePullbackInclusion Λ gX.hom).symm (F Λ c') ≪≫
    Functor.associator P₀ I (F Λ c') ≪≫ Functor.isoWhiskerLeft P₀ τ

/-- The ambient native refinement diagram, with its existing functor laws.
Source: lem-fix-weil-operations.proof.md, paragraph 1, common refinements
(blueprint: lem-pod-semilinear-field-operation-lifts).
The explicit native laws avoid rebuilding their derived-category components. -/
def podAmbientCompactificationDiagram {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Compactification f)ᵒᵖ ⥤ (D Λ X ⥤ D Λ Y) where
  obj c := F Λ c.unop
  map r := refinement Λ r.unop
  map_id c := (refinement_id_comp Λ c.unop
    (Compactification.Refinement.id c.unop) (Compactification.Refinement.id c.unop)).1
  map_comp {c₁ _c₂ _c₃} r t := (refinement_id_comp Λ c₁.unop t.unop r.unop).2

/-- Restrict the native diagram to the original bounded inputs by whiskering.
Source: lem-fix-weil-operations.proof.md, paragraph 1, common refinements
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podCompactificationDiagram {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Compactification f)ᵒᵖ ⥤
      (BoundedConstructible (condensedRingObj Λ X) ⥤ D Λ Y) :=
  podAmbientCompactificationDiagram Λ f ⋙
    (Functor.whiskeringLeft (BoundedConstructible (condensedRingObj Λ X))
      (D Λ X) (D Λ Y)).obj (boundedConstructible (condensedRingObj Λ X)).ι

/-- The comparison data type, with the native ambient functors kept folded.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodCompactificationComparisonFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ c₁ c₂ : Compactification f,
    (podCompactificationDiagram Λ f).obj (op c₁) ≅
      (podCompactificationDiagram Λ f).obj (op c₂)

/-- The four native common-refinement clauses, stated through the native diagram.
Its objects are the original bounded-input compactification functors, and its maps
are precisely the restricted native refinement transformations.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodCompactificationComparisonCoherence {X Y : Scheme.{u}} {f : X ⟶ Y}
    (τ : PodCompactificationComparisonFamily Λ f) : Prop :=
  (∀ (c₁ c₂ d : Compactification f) (h₁ : d ⟶ c₁)
      (h₂ : d ⟶ c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
    (τ c₁ c₂).hom.app K ≫ ((podCompactificationDiagram Λ f).map h₂.op).app K =
      ((podCompactificationDiagram Λ f).map h₁.op).app K) ∧
  (∀ c : Compactification f, τ c c = Iso.refl _) ∧
  (∀ c₁ c₂ c₃ : Compactification f, τ c₁ c₂ ≪≫ τ c₂ c₃ = τ c₁ c₃) ∧
  ∀ σ : PodCompactificationComparisonFamily Λ f,
    (∀ (c₁ c₂ d : Compactification f) (h₁ : d ⟶ c₁)
        (h₂ : d ⟶ c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
      (σ c₁ c₂).hom.app K ≫ ((podCompactificationDiagram Λ f).map h₂.op).app K =
        ((podCompactificationDiagram Λ f).map h₁.op).app K) → σ = τ

private theorem podRestrictedMapIsIso {C B : Type*} [Category* C] [Category* B]
    (I : ObjectProperty C) {F G : C ⥤ B} (α : F ⟶ G)
    (h : ∀ K, I K → IsIso (α.app K)) : IsIso (Functor.whiskerLeft I.ι α) := by
  have : ∀ K : I.FullSubcategory,
      IsIso ((Functor.whiskerLeft I.ι α).app K) := fun K ↦ h K.obj K.property
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this

/-- Rational refinement is invertible on the original bounded constructible inputs.
Source: the native rational refinement theorem, with no new hypotheses
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: apply native refinement invertibility to every component; natural
transformations with invertible components are invertible. -/
theorem podCompactificationDiagram_map_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {c₁ c₂ : Compactification f}
    (r : c₁ ⟶ c₂) : IsIso ((podCompactificationDiagram Λ f).map r.op) := by
  exact podRestrictedMapIsIso (boundedConstructible (condensedRingObj Λ X)) (refinement Λ r)
    (fun K hK ↦ rational_refinement_isIso Λ ℓ hΛ k r K hK)

/-- Construct the normalized comparison through a genuine common refinement.
The cofiltered compactification category is proved in the source library; inverse
refinement maps are uniquely determined by native rational refinement invertibility.
Source: lem-fix-weil-operations.proof.md, paragraph 1, common refinements
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
@[irreducible] def podCanonicalCompactificationComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    PodCompactificationComparisonFamily Λ f :=
  cofilteredIsoComparison (podCompactificationDiagram Λ f)
    (fun r ↦ podCompactificationDiagram_map_isIso Λ ℓ hΛ k f r)

private theorem podCofilteredComparisonCoherent
    {C A B : Type*} [Category* C] [Category* A] [Category* B]
    [IsCofilteredOrEmpty C] (H : Cᵒᵖ ⥤ (A ⥤ B))
    (hH : ∀ {i j : C} (r : i ⟶ j), IsIso (H.map r.op)) :
    (∀ (i j d : C) (u : d ⟶ i) (v : d ⟶ j) (K : A),
      (cofilteredIsoComparison H hH i j).hom.app K ≫ (H.map v.op).app K =
        (H.map u.op).app K) ∧
    (∀ i, cofilteredIsoComparison H hH i i = Iso.refl _) ∧
    (∀ i j k, cofilteredIsoComparison H hH i j ≪≫
      cofilteredIsoComparison H hH j k = cofilteredIsoComparison H hH i k) ∧
    ∀ σ : ∀ i j, H.obj (op i) ≅ H.obj (op j),
      (∀ (i j d : C) (u : d ⟶ i) (v : d ⟶ j) (K : A),
        (σ i j).hom.app K ≫ (H.map v.op).app K = (H.map u.op).app K) →
      σ = cofilteredIsoComparison H hH := by
  refine ⟨?_, cofilteredIsoComparison_refl H hH,
    cofilteredIsoComparison_trans H hH, ?_⟩
  · intro i j d u v K
    exact congrArg (fun α : H.obj (op i) ⟶ H.obj (op d) ↦ α.app K)
      (cofilteredIsoComparison_normalized H hH u v)
  · intro σ hσ
    apply cofilteredIsoComparison_unique H hH σ
    intro i j d u v
    apply NatTrans.ext
    funext K
    exact hσ i j d u v K

/-- The constructed family has normalization, identity, cocycle and uniqueness.
Source: lem-fix-weil-operations.proof.md, paragraph 1, common refinements
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: normalization is common-refinement cancellation. Apply it to identity
cones and a cone over three compactifications for identity and cocycle. Cancel
an invertible refinement to prove uniqueness of every normalized family. -/
theorem podCanonicalCompactificationComparison_coherent (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    PodCompactificationComparisonCoherence Λ
      (podCanonicalCompactificationComparison Λ ℓ hΛ k f) := by
  unfold PodCompactificationComparisonCoherence podCanonicalCompactificationComparison
  exact podCofilteredComparisonCoherent (podCompactificationDiagram Λ f)
    (fun r ↦ podCompactificationDiagram_map_isIso Λ ℓ hΛ k f r)

/-- The normalized family exists with all four clauses on precisely the native domain.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: take the constructed cofiltered comparison and its proved coherence. -/
theorem pod_compactification_comparison_family_exists (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ τ : PodCompactificationComparisonFamily Λ f,
      PodCompactificationComparisonCoherence Λ τ :=
  ⟨podCanonicalCompactificationComparison Λ ℓ hΛ k f,
    podCanonicalCompactificationComparison_coherent Λ ℓ hΛ k f⟩

/-- The native rational compact-support lift for any chosen compactification.
Its comparison is fixed to the existing normalized common-refinement family;
its normalization, identity and cocycle remain those of that native family.
The scheme automorphisms may be semilinear and the models need not be separated.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: replace (i,p) by (g_X i,p g_Y inverse). The identity on its middle
scheme gives an isomorphism square, so its specified proper/open exchange is
invertible. The unique normalized native comparison returns to the chosen
compactification on the original bounded constructible inputs. Compose that
comparison, whiskered by constructible pullback, with the exchange. Apply the
proved covariant calculation to this very composite. -/
theorem pod_reindexed_compact_field_lift (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (gX : X ≅ X) (gY : Y ≅ Y)
    (w : gX.hom ≫ f = f ≫ gY.hom) :
    PodCovariantWeilLiftSpec
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c)
      (podReindexedCompactComparison Λ c gX gY w
        (podCanonicalCompactificationComparison Λ ℓ hΛ k f
          (podTransportCompactification c gX gY w) c)) := by
  exact pod_covariant_field_operation_lift
    (P := podConstructiblePullback Λ gX.hom) (Q := P Λ gY.hom)
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c)
    (podReindexedCompactComparison Λ c gX gY w
      (podCanonicalCompactificationComparison Λ ℓ hΛ k f
        (podTransportCompactification c gX gY w) c))

/-- Semilinear Frobenius geometry and exact native condensed field transport.
No linearity over the algebraic closure is imposed on the Frobenius automorphisms.
The covariant operation comparisons are `pod_actual_pullback_field_lifts` and
`pod_reindexed_compact_field_lift`; tensor and restricted Hom are included in the
transport specifications, retaining their canonical comparisons.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: the Cartesian Frobenius-square theorem supplies the square and commutativity.
The equation of structure maps follows from that commutativity and the fact that the
base-changed f is over the algebraic closure. Apply exact scheme-isomorphism transport
separately to the two geometric Frobenii. -/
theorem semilinearFieldOperationLifts (D₀ : FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    IsPullback (D₀.geometricFrobenius X₀).hom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).map f₀).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).map f₀).left
      (D₀.geometricFrobenius Y₀).hom ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).map f₀).left ≫
        (D₀.geometricFrobenius Y₀).hom ≫ (D₀.geometricFiber Y₀).hom =
      (D₀.geometricFrobenius X₀).hom ≫ (D₀.geometricFiber X₀).hom ∧
    PodFieldOperationTransportSpec Λ (D₀.geometricFiber X₀).left
      (D₀.geometricFrobenius X₀) ∧
    PodFieldOperationTransportSpec Λ (D₀.geometricFiber Y₀).left
      (D₀.geometricFrobenius Y₀) := by
  have hgeom := D₀.frobenius_square_cartesian X₀ Y₀ f₀
  refine ⟨hgeom.2.2.2.2.2.1, ?_, pod_field_transport Λ _ _, pod_field_transport Λ _ _⟩
  have hc : (D₀.geometricFrobenius X₀).hom ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).map f₀).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).map f₀).left ≫
        (D₀.geometricFrobenius Y₀).hom := hgeom.2.2.2.2.1
  rw [← Category.assoc, ← hc, Category.assoc]
  congr 1
  exact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap D₀.k₀ D₀.k)))).map f₀).w

end WeilConjectures
