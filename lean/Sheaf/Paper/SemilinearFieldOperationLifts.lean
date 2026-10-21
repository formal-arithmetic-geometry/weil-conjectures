/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.SixFunctors.FrobeniusSquareCartesian
public import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PullbackIdentitiesScalarExtension
public import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.Paper.FrobeniusCompactSupportExchange

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
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry Opposite
open CategoryTheory.SuppliedExchangeProjection
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
  sorry

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
  sorry

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
  sorry


/-- The rational Frobenius square component through the canonical compositors.
Source: blueprint prop-weil-operations, sentence 1, proof step 4
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def podRationalSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
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
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
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
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    (fun [hx : ∀ x : (D.geometricFiber X₀).left,
        Invertible (l : (D.geometricFiber X₀).left.residueField x)]
      [hy : ∀ y : (D.geometricFiber Y₀).left,
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
      (hx := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
      (hy := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y) := by
  sorry


variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]

/-- Integral and rational Frobenius transport, using the existing prime-invertibility
data, canonical inverse-image realization, and the actual inverse scheme map.
Source: blueprint prop-weil-operations, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts). -/
def PodRationalFrobeniusTransportSpec
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
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
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
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

/-- Semilinear Frobenius geometry, exact field transport, and the canonical tensor
and internal-Hom lifts on both models. The covariant lifts, including the specified
Ex_* and Ex_!, are `pod_supplied_field_operation_lifts`; their explicit object and
arrow calculation is `pod_covariant_field_operation_lift`.
Source: blueprint main-20261015, prop-weil-operations.proof.md, sentence 1
(blueprint: lem-pod-semilinear-field-operation-lifts).

Proof, following all nine node steps:
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
equivalences make it invertible by lem-weil-mate-iso-along-equivalences. For Ex_!
use lem-pod-weil-frobenius-compact-support-exchange on its original preserved domain.
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
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    IsPullback (D.geometricFrobenius X₀).hom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      (D.geometricFrobenius Y₀).hom ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        (D.geometricFrobenius Y₀).hom ≫ (D.geometricFiber Y₀).hom =
      (D.geometricFrobenius X₀).hom ≫ (D.geometricFiber X₀).hom ∧
    PodFieldOperationTransportSpec D l hl X₀ E Ω ∧
    PodFieldOperationTransportSpec D l hl Y₀ E Ω := by
  sorry

end WeilConjectures
