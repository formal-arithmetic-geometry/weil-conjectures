/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralUniformCoefficient
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ContinuousCoefficientRealizations
import all Sheaf.Paper.PbcScalarExtension
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientPullbackIso
import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso

/-! # Balanced localization of finite coefficient extensions

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E and 0D6D;
Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-scalar-balanced-localization).

The coefficient map is postcomposition, not a chosen ring map. Tensor comparisons
are the existing unit-normalized comparisons. Raw fractions retain integral Hom torsion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)

/-- A finite coefficient embedding is continuous for the specified spectral topologies.
Source: BS 6.8.2; uniqueness of the extended absolute value
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: pull back the spectral absolute value on F along i. Uniqueness identifies it
with the spectral absolute value on E. Apply the resulting distance equality to
x-y; i is an isometry, hence continuous. -/
theorem rationalBalancedEmbedding_continuous :
    @Continuous E F
      ((coefficientExtensionNormedField l E).toMetricSpace.toPseudoMetricSpace.toUniformSpace
        ).toTopologicalSpace
      ((coefficientExtensionNormedField l F).toMetricSpace.toPseudoMetricSpace.toUniformSpace
        ).toTopologicalSpace i := by
  let := coefficientExtensionNormedField l E
  let := coefficientExtensionNormedField l F
  have hi : Isometry i := by
    apply AddMonoidHomClass.isometry_of_norm i
    intro x
    exact WeilConjectures.integralScalar_absoluteValue l E F i x
  exact hi.continuous

/-- Postcompose continuous field-valued functions by the actual coefficient embedding.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedCoefficient (X : Scheme.{u}) :
    rationalCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X F := by
  letI := coefficientExtensionNormedField l E
  letI := coefficientExtensionNormedField l F
  exact continuousCoefficientMap
    (RingHom.ulift i.toRingHom : ULift.{u + 1} E →+* ULift.{u + 1} F)
    (continuous_uliftUp.comp
      ((rationalBalancedEmbedding_continuous l E F i).comp continuous_uliftDown)) X

/-- The finite-projection normalization and the completed geometric square.
Source: BS 6.8.2, finite-projection construction
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: the embedding sends t_E into the maximal ideal of F; write it as u t_F^e,
e ≥ 1. Thus the same-index quotient maps exist. The universal limit map has the
stated projections. Compose the geometric square with every target projection:
postcomposition of locally constant residues commutes with geometric precomposition.
Joint monicity of the limit projections gives the square. -/
theorem rationalBalancedIntegralCoefficients (X : Scheme.{u}) :
    (∀ n : ℕ, pbcScalarCoefficientMap l E F i X ≫
        pbcAdicProjection X (pbcIntegralDatum l F) n =
      pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        AdicCoefficients.coefficientMap X (pbcScalarQuotientMap l E F i n)) ∧
    (∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (pbcScalarCoefficientMap l E F i X) ≫ completedCoefficientMap g (pbcIntegralDatum l F) =
        completedCoefficientMap g (pbcIntegralDatum l E) ≫ pbcScalarCoefficientMap l E F i Y) := by
  refine ⟨(pbcScalarCoefficientMap_exists l E F i X).exists.choose_spec, ?_⟩
  intro Y g
  let c (W : Scheme.{u}) := pbcScalarCoefficientMap l E F i W
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hc (W : Scheme.{u}) (n : ℕ) :
      c W ≫ pbcAdicProjection W (pbcIntegralDatum l F) n =
        pbcAdicProjection W (pbcIntegralDatum l E) n ≫
          AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i W).exists.choose_spec n
  apply limit.hom_ext
  intro n
  change (L.map (c X) ≫ completedCoefficientMap g (pbcIntegralDatum l F)) ≫
      pbcAdicProjection Y (pbcIntegralDatum l F) n.unop =
    (completedCoefficientMap g (pbcIntegralDatum l E) ≫ c Y) ≫
      pbcAdicProjection Y (pbcIntegralDatum l F) n.unop
  simp only [Category.assoc, hc]
  rw [scalarCompletedCoefficientMap_projection]
  rw [← Category.assoc (completedCoefficientMap g (pbcIntegralDatum l E)),
    scalarCompletedCoefficientMap_projection]
  rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ L.map (pbcAdicProjection X (pbcIntegralDatum l E) n.unop) ≫ k)
    (scalarFiniteCoefficientMap_naturality g (pbcIntegralDatum l E)
      (pbcIntegralDatum l F) n.unop (pbcScalarQuotientMap l E F i n.unop))

private theorem rationalBalancedConstant_value (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (a : E) (x : U.unop.left) :
    rationalCoefficientValue l E X U
      ((rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a))) x = a := by
  let := coefficientExtensionNormedField l E
  let η : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)) ⟶
      (rationalCoefficientSheaf l X E).obj :=
    { app := fun _ ↦ CommRingCat.ofHom
        { toFun := fun b ↦ ContinuousMap.const _ b
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }
  have hc : toSheafify (ProEt.topology X) _ ≫ (rationalModuleConstantMap l E X).hom =
      η := toSheafify_sheafifyLift (ProEt.topology X) η _
  have hv := ConcreteCategory.congr_hom (congr_app hc U) (ULift.up a : ULift.{u + 1} E)
  exact congrArg (fun b ↦ rationalCoefficientValue l E X U b x) hv

/-- The localized map has the pointwise inclusion formula and preserves reciprocals.
The unit and inverse equations include empty site objects.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: postcomposition gives the section formula. Apply the field embedding to
1 and a*a⁻¹=1 and then take constant functions. The reciprocal is the constant
function with value i(a⁻¹), even if the integral Hom groups contain torsion. -/
theorem rationalBalancedCoefficient_sections (X : Scheme.{u}) :
    (∀ (U : X.ProEtᵒᵖ) (b : (rationalCoefficientSheaf l X E).obj.obj U)
      (x : U.unop.left),
      rationalCoefficientValue l F X U
          ((rationalBalancedCoefficient l E F i X).hom.app U b) x =
        i (rationalCoefficientValue l E X U b x)) ∧
    (∀ U : X.ProEtᵒᵖ, (rationalBalancedCoefficient l E F i X).hom.app U 1 = 1) ∧
    (∀ (U : X.ProEtᵒᵖ) (a : E), a ≠ 0 →
      ((rationalBalancedCoefficient l E F i X).hom.app U
        ((rationalModuleConstantMap l E X).hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
              (ULift.up a)))) *
        ((rationalModuleConstantMap l F X).hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} F)))).app U
              (ULift.up (i a⁻¹)))) = 1) := by
  refine ⟨fun _ _ _ ↦ rfl,
    fun U ↦ ((rationalBalancedCoefficient l E F i X).hom.app U).hom.map_one, ?_⟩
  intro U a ha
  let := coefficientExtensionNormedField l F
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change i (rationalCoefficientValue l E X U
      ((rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a))) x) *
    rationalCoefficientValue l F X U
      ((rationalModuleConstantMap l F X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} F)))).app U
            (ULift.up (i a⁻¹)))) x = 1
  rw [rationalBalancedConstant_value, rationalBalancedConstant_value,
    ← map_mul, mul_inv_cancel₀ ha, map_one]

variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
variable (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)

/-- Integral coefficient inclusion is postcomposition under the specified realizations.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: compose with every finite quotient projection. The residue of i(a) is the
quotient inclusion applied to the residue of a; the normalized integral realization
has precisely these finite components. Equality into the inverse limit proves the
claim, and pointwise evaluation gives the displayed equation. -/
theorem rationalBalancedIntegralNormalization
    (U : X.ProEtᵒᵖ) (b : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) :
    (integralCoefficientValue l F X U
      ((sE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i X ≫ sF.integralIso.hom).hom.app
        U b) x).val = i (integralCoefficientValue l E X U b x).val := by
  sorry


/-- The specific completed integral map localizes to continuous postcomposition.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: under the quotient-normalized integral realizations, each residue of the
integral inclusion is postcomposition by the quotient inclusion. Uniqueness into
the inverse limit identifies the map on integral functions. Localizing sends
b/t_E^n to i(b)i(t_E)^(-n); pointwise reciprocals show this is well defined and
unital. The specified numerator normalizations of sE and sF give the equation. -/
theorem rationalBalancedCoefficient_square :
    pbcScalarCoefficientMap l E F i X ≫ (sF.integralIso.hom ≫ sF.inclusion) =
      (sE.integralIso.hom ≫ sE.inclusion) ≫ rationalBalancedCoefficient l E F i X := by
  apply (cancel_epi sE.integralIso.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply Sheaf.hom_ext
  ext U b
  apply rationalCoefficientValue_ext l F X U
  intro x
  change rationalCoefficientValue l F X U
      (sF.inclusion.hom.app U
        ((sE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i X ≫
          sF.integralIso.hom).hom.app U b)) x =
    i (rationalCoefficientValue l E X U (sE.inclusion.hom.app U b) x)
  exact (sF.inclusion_normalization U.unop _ x).trans
    ((rationalBalancedIntegralNormalization l E F i X sE sF U b x).trans
      (congrArg i (sE.inclusion_normalization U.unop b x)).symm)

/-- The s comparison, with common target F_X tensor over B_E,X.
Source: Stacks 0D6D (blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedS (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :=
  pbcReductionNormalization (pbcScalarCoefficientMap l E F i X)
    (sF.integralIso.hom ≫ sF.inclusion)
    ((sE.integralIso.hom ≫ sE.inclusion) ≫ rationalBalancedCoefficient l E F i X)
    (rationalBalancedCoefficient_square l E F i X sE sF) K

/-- The t comparison to the same single derived tensor.
Source: Stacks 0D6D (blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedT (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :=
  pbcReductionNormalization (sE.integralIso.hom ≫ sE.inclusion)
    (rationalBalancedCoefficient l E F i X)
    ((sE.integralIso.hom ≫ sE.inclusion) ≫ rationalBalancedCoefficient l E F i X) rfl K

/-- The component s followed by t inverse, transported by the recorded J object equations.
Source: BS 6.8.14(2); Stacks 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedComponent
    (K : PbcRationalDerivedCategory l E X Fact.out Fact.out) :
    sF.J.obj ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≅
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj (sE.J.obj K) :=
  eqToIso (sF.objects ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj K.obj)) ≪≫
    rationalBalancedS l E F i X sE sF K.obj.obj ≪≫
    (rationalBalancedT l E F i X sE K.obj.obj).symm ≪≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).mapIso
      (eqToIso (sE.objects K.obj)).symm

/-- The specified components are natural for every raw fraction morphism.
Source: BS 6.8.14(2); Stacks 00CO and 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: on integral morphisms use naturality of the two unit-normalized derived
composition comparisons. The scalar action moves across tensor balancing, so the
equation for f/t_E^n is that integral equation times i(t_E)^(-n). If a further
power kills a difference of numerators, multiply its image by the inverse of
that power and both denominators. This proves descent without a torsion-free
assumption, and gives naturality for arbitrary raw Hom elements. -/
theorem rationalBalancedComponent_naturality
    {K L : PbcRationalDerivedCategory l E X Fact.out Fact.out} (f : K ⟶ L) :
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J).map f ≫
        (rationalBalancedComponent l E F i X sE sF L).hom =
      (rationalBalancedComponent l E F i X sE sF K).hom ≫
        (sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map f := by
  sorry

/-- The natural isomorphism on raw rationalizations, with its actual inverse components.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedTheta :
    pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J ≅
      sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X) :=
  NatIso.ofComponents (rationalBalancedComponent l E F i X sE sF)
    (rationalBalancedComponent_naturality l E F i X sE sF)

section TensorModels
variable {W : Scheme.{u}}
  {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
  (a : R ⟶ S) (b : S ⟶ B)

/-- The ordinary multiplication comparison for the very same scalar-extension functors.
Source: Stacks 03EK, 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedOrdinaryComp :
    pbcExtend a ⋙ pbcExtend b ≅ pbcExtend (a ≫ b) :=
  Adjunction.leftAdjointCompIso (pbcScalarAdjunction a) (pbcScalarAdjunction b)
    (pbcScalarAdjunction (a ≫ b)) (pbcRestrictComp a b (a ≫ b) rfl)

/-- Multiplication, insertion of one, and descent on every flat-term K-flat model.
This applies to both factorizations defining s and t, without quotient flatness
or boundedness assumptions.
Source: Stacks 0G7E and 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: apply K-flat pullback preservation to the identity underlying topos and a.
The normalized ordinary adjunction identifies its composite left adjoint with
extension along a followed by b. On pure sections this map is multiplication;
the inverse inserts one, and balancing gives both inverse equations. The maps
commute with differentials. Derive the unit-normalized adjunctions using a
flat-term K-flat resolution. Their computation counits give the displayed
representative equation. Universality descends naturality to every derived map
and proves independence of the representative. -/
theorem rationalBalancedTensorModels :
    (∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U)
      (s : S.obj.obj U) (t : B.obj.obj U),
      ((rationalBalancedOrdinaryComp a b).hom.app M).val.app U
          (pbcTensorSection b ((pbcExtend a).obj M) U t (pbcTensorSection a M U s x)) =
        pbcTensorSection (a ≫ b) M U (t * b.hom.app U s) x) ∧
    (∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) (t : B.obj.obj U),
      ((rationalBalancedOrdinaryComp a b).inv.app M).val.app U
          (pbcTensorSection (a ≫ b) M U t x) =
        pbcTensorSection b ((pbcExtend a).obj M) U t (pbcTensorSection a M U 1 x)) ∧
    (∀ P : CochainComplex (pbcModules W R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := R) (P.X n)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := S)
          (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P) ∧
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := S)
          ((((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P).X n))) ∧
    (∀ P : CochainComplex (pbcModules W R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := R) (P.X n)) →
      (pbcReductionNormalization a b (a ≫ b) rfl (DerivedCategory.Q.obj P)).hom ≫
          pbcComplexCounit (a ≫ b) P =
        (pbcDerivedExtend b).map (pbcComplexCounit a P) ≫
          pbcComplexCounit b (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (rationalBalancedOrdinaryComp a b)
              (.up ℤ)).hom.app P)) := by
  sorry
end TensorModels

private theorem rationalBalancedFractions_eq
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) {K L : C} (f h : K ⟶ L) (r m n : ℕ)
    (heq : p ^ r • (p ^ m • f - p ^ n • h) = 0) :
    (IsLocalization.Away.invSelf (S := Localization.Away p) p) ^ n •
        (ScalarLocalization.localization R C p).map f =
      (IsLocalization.Away.invSelf (S := Localization.Away p) p) ^ m •
        (ScalarLocalization.localization R C p).map h := by
  let Q := ScalarLocalization.localization R C p
  let _ : Q.Additive := ScalarLocalization.localizationAdditive _ _ _
  let c := algebraMap R (Localization.Away p) p
  let v : Localization.Away p := IsLocalization.Away.invSelf p
  have hv (a : ℕ) : c ^ a * v ^ a = 1 := by
    rw [← mul_pow]
    exact congrArg (fun z : Localization.Away p ↦ z ^ a)
      (IsLocalization.Away.mul_invSelf p) |>.trans (one_pow a)
  have hzero : Q.map (0 : K ⟶ L) = 0 := TensorProduct.tmul_zero _ _
  have hz := congrArg Q.map heq
  rw [Q.map_smul, Q.map_sub, Q.map_smul, Q.map_smul, hzero] at hz
  have hsmul (a : R) (z : Q.obj K ⟶ Q.obj L) :
      algebraMap R (Localization.Away p) a • z = a • z :=
    algebraMap_smul (M := Localization.Away p ⊗[R] (K ⟶ L)) (Localization.Away p) a z
  have hcross : c ^ m • Q.map f = c ^ n • Q.map h := by
    apply sub_eq_zero.mp
    apply ((IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away p) p r).smul_left_cancel).mp
    simpa only [c, ← map_pow, hsmul, smul_zero] using hz
  have hq : v ^ n • Q.map f = v ^ m • Q.map h := by
    apply ((IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away p) p (m + n)).smul_left_cancel).mp
    calc
      c ^ (m + n) • (v ^ n • Q.map f) = c ^ m • Q.map f := by
        rw [pow_add, smul_smul, mul_assoc, hv, mul_one]
      _ = c ^ n • Q.map h := hcross
      _ = c ^ (m + n) • (v ^ m • Q.map h) := by
        rw [Nat.add_comm m n, pow_add, smul_smul, mul_assoc, hv, mul_one]
  exact hq

/-- Integral naturality extends to fractions, including the annihilating-power relation.
The equality holds for each of the two compared functors. No torsion-freeness is used.
Source: Stacks 00CO; BS 6.8.14(2)
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: if t^r(t^m f-t^n h)=0, semilinearity gives the same annihilating equation
after either integral tensor. In the target the constant i(t) is invertible.
Multiply by i(t)^(-r-m-n) to obtain equality of the two fraction images.
For naturality multiply the integral equation by i(t)^(-n); scalar multiplication
commutes with the balanced comparison. -/
theorem rationalBalancedFractions
    (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
    (f h : K ⟶ L) (r m n : ℕ)
    (heq : pbcUniformizer l E ^ r •
      (pbcUniformizer l E ^ m • f - pbcUniformizer l E ^ n • h) = 0) :
    (sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        ((IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
          (pbcUniformizer l E)) ^ n •
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      (sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        ((IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
          (pbcUniformizer l E)) ^ m •
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map h) ∧
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J).map
        ((IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
          (pbcUniformizer l E)) ^ n •
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      (pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J).map
        ((IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
          (pbcUniformizer l E)) ^ m •
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map h) := by
  have hq := rationalBalancedFractions_eq (pbcUniformizer l E) f h r m n heq
  exact ⟨congrArg
    (sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map hq,
    congrArg (pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J).map hq⟩

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G) (sG : RationalModuleRealization l G X)

set_option linter.unusedSectionVars false in
/-- Continuous postcomposition composes as the given field embeddings do.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: on each section both composites are pointwise j(i(f(x))). -/
theorem rationalBalancedCoefficient_comp :
    rationalBalancedCoefficient l E F i X ≫ rationalBalancedCoefficient l F G j X =
      rationalBalancedCoefficient l E G (j.comp i) X := by
  ext U b
  rfl

/-- Successive theta comparisons agree with the specified direct raw associator.
This is an equation on the raw categories, so includes every fractional arrow.
Source: Stacks 0D6D; BS 6.8.14(2)
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: substitute s followed by t inverse for each component. On a common flat-term
K-flat model the middle inverse comparisons cancel, and both routes multiply the
adjacent coefficients. Derived composition normalization identifies those chain maps.
The specified raw associator is the rationalization of that normalization. Scalar
localization preserves composition, whiskering and this equality, by the annihilating
power calculation used for rationalBalancedFractions. -/
theorem rationalBalancedTower
    (K : PbcRationalDerivedCategory l E X Fact.out Fact.out) :
    sG.J.map ((pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app K) ≫
        (rationalBalancedTheta l E G (j.comp i) X sE sG).hom.app K =
      (rationalBalancedTheta l F G j X sF sG).hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map
          ((rationalBalancedTheta l E F i X sE sF).hom.app K) ≫
        (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
          (rationalBalancedCoefficient l F G j X)
          (rationalBalancedCoefficient l E G (j.comp i) X)
          (rationalBalancedCoefficient_comp l E F i X G j) (sE.J.obj K)).hom := by
  sorry


variable (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
  (k : G →ₐ[ℚ_[l]] H)

/-- The four-field balanced pentagon, evaluated after realization on every raw object.
Both routes flatten to the product of the three degree-zero coefficients.
Source: Stacks 0D6D (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: on a flat-term K-flat representative each route sends n tensor m tensor l
tensor p to nml tensor p. Associativity gives equality of these chain maps, and
canonical derived computation identifies their images. The raw scalar associators
are the specified rationalized balanced comparisons, including tensor units for
repeated fields. Localization preserves their composite and whiskered equations. -/
theorem rationalBalancedPentagon (sH : RationalModuleRealization l H X)
    (K : PbcRationalDerivedCategory l E X Fact.out Fact.out) :
    sH.J.map
        ((pbcRationalScalarExtension l G H k X Fact.out Fact.out).map
            ((pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app K) ≫
          (pbcRationalScalarComp l E G H (j.comp i) k X Fact.out Fact.out).hom.app K) ≫
        (rationalBalancedTheta l E H (k.comp (j.comp i)) X sE sH).hom.app K =
      sH.J.map
        ((pbcRationalScalarComp l F G H j k X Fact.out Fact.out).hom.app
            ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≫
          (pbcRationalScalarComp l E F H i (k.comp j) X Fact.out Fact.out).hom.app K) ≫
        (rationalBalancedTheta l E H ((k.comp j).comp i) X sE sH).hom.app K := by
  sorry

/-- Equality coefficients have the multiplication unitor, with its cochain computation.
Conjugation by the published raw tensor unit makes the raw source functor literally id.
Source: BS 6.8.14(2); Stacks 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: the identity coefficient map is pointwise identity. Ordinary tensor
multiplication a tensor m to am has inverse m to 1 tensor m. Derive this
comparison through the universal computation counit. Substitute the normalized s
and t formulas in theta. The result composed with multiplication is realization
of the specified raw tensor unit. Conjugation by that unit gives the literal
identity comparison; all unit equations reduce to 1x=x=x1. -/
theorem rationalBalancedIdentity :
    rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X = 𝟙 _ ∧
    ∃ (o : pbcExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X) ≅ 𝟭 _)
      (d : pbcDerivedExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X) ≅ 𝟭 _),
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (U : X.ProEtᵒᵖ)
        (a : (rationalCoefficientSheaf l X E).obj.obj U) (m : M.val.obj U),
        (o.hom.app M).val.app U
            (pbcTensorSection (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X)
              M U a m) = a • m) ∧
      (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X) P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P)) ∧
      (∀ K : PbcRationalDerivedCategory l E X Fact.out Fact.out,
        (rationalBalancedTheta l E E (AlgHom.id ℚ_[l] E) X sE sE).hom.app K ≫
            d.hom.app (sE.J.obj K) =
          sE.J.map ((pbcRationalScalarUnit l E X Fact.out Fact.out).hom.app K)) := by
  sorry

private theorem rationalBalancedNormalizeTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂} {H H' : C₀ ⥤ C₂}
    {J₀ : C₀ ⥤ D₀} {J₁ : C₁ ⥤ D₁} {J₂ : C₂ ⥤ D₂}
    {L : D₀ ⥤ D₁} {M : D₁ ⥤ D₂} {N : D₀ ⥤ D₂}
    (σ : F ≅ F') (τ : G ≅ G') (υ : H ≅ H') (α : F ⋙ G ≅ H)
    (a : F ⋙ J₁ ≅ J₀ ⋙ L) (b : G ⋙ J₂ ≅ J₁ ⋙ M) (c : H ⋙ J₂ ≅ J₀ ⋙ N)
    (K : C₀) (β : M.obj (L.obj (J₀.obj K)) ⟶ N.obj (J₀.obj K))
    (h : J₂.map (α.hom.app K) ≫ c.hom.app K =
      b.hom.app (F.obj K) ≫ M.map (a.hom.app K) ≫ β) :
    J₂.map ((isoWhiskerRight σ.symm G' ≪≫ isoWhiskerLeft F τ.symm ≪≫ α ≪≫ υ).hom.app K) ≫
        (isoWhiskerRight υ.symm J₂ ≪≫ c).hom.app K =
      (isoWhiskerRight τ.symm J₂ ≪≫ b).hom.app (F'.obj K) ≫
        M.map ((isoWhiskerRight σ.symm J₁ ≪≫ a).hom.app K) ≫ β := by
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, Functor.map_comp, Category.assoc]
  have hυ : J₂.map (υ.hom.app K) ≫ J₂.map (υ.inv.app K) = 𝟙 _ := by
    rw [← J₂.map_comp, Iso.hom_inv_id_app, J₂.map_id]
  rw [reassoc_of% hυ, h]
  rw [← J₂.map_comp_assoc, τ.inv.naturality, J₂.map_comp]
  rw [Category.assoc, ← reassoc_of% b.hom.naturality (σ.inv.app K)]

/-- The same theta tower equation after the specified literal-identity normalization.
No new rationalization or associator is introduced.
Source: BS 6.8.14(2); Stacks 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: apply rationalBalancedTower and conjugate by pbcStageNormalization on the
three edges. The definition of pbcStageAssociator is that identical conjugation
of pbcRationalScalarComp. The normalization maps cancel, so the equation remains
true on raw objects and fractions, including equal adjacent fields. -/
theorem rationalBalancedNormalizedTower
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    {A B C : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B) (h' : B ≤ C)
    (rA : RationalModuleRealization l A.val X) (rB : RationalModuleRealization l B.val X)
    (rC : RationalModuleRealization l C.val X) (K : pbcCoefficientStage l Ω X A) :
    rC.J.map ((pbcStageAssociator l Ω X h h').hom.app K) ≫
        ((Functor.isoWhiskerRight (pbcStageNormalization l Ω X (h.trans h')).symm rC.J) ≪≫
          rationalBalancedTheta l A.val C.val (pbcSubfieldInclusion l Ω (h.trans h'))
            X rA rC).hom.app K =
      ((Functor.isoWhiskerRight (pbcStageNormalization l Ω X h').symm rC.J) ≪≫
          rationalBalancedTheta l B.val C.val (pbcSubfieldInclusion l Ω h')
            X rB rC).hom.app ((pbcStageTransition l Ω X h).obj K) ≫
        (pbcDerivedExtend
          (rationalBalancedCoefficient l B.val C.val (pbcSubfieldInclusion l Ω h') X)).map
          (((Functor.isoWhiskerRight (pbcStageNormalization l Ω X h).symm rB.J) ≪≫
            rationalBalancedTheta l A.val B.val (pbcSubfieldInclusion l Ω h)
              X rA rB).hom.app K) ≫
        (pbcReductionNormalization
          (rationalBalancedCoefficient l A.val B.val (pbcSubfieldInclusion l Ω h) X)
          (rationalBalancedCoefficient l B.val C.val (pbcSubfieldInclusion l Ω h') X)
          (rationalBalancedCoefficient l A.val C.val
            ((pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h)) X)
          (rationalBalancedCoefficient_comp l A.val B.val (pbcSubfieldInclusion l Ω h)
            X C.val (pbcSubfieldInclusion l Ω h')) (rA.J.obj K)).hom := by
  simpa only [pbcStageAssociator, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id] using
    rationalBalancedNormalizeTower
      (pbcStageNormalization l Ω X h) (pbcStageNormalization l Ω X h')
      (pbcStageNormalization l Ω X (h.trans h'))
      (pbcRationalScalarComp l A.val B.val C.val
        (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') X Fact.out Fact.out)
      (rationalBalancedTheta l A.val B.val (pbcSubfieldInclusion l Ω h) X rA rB)
      (rationalBalancedTheta l B.val C.val (pbcSubfieldInclusion l Ω h') X rB rC)
      (rationalBalancedTheta l A.val C.val (pbcSubfieldInclusion l Ω (h.trans h')) X rA rC)
      K _ (rationalBalancedTower l A.val B.val (pbcSubfieldInclusion l Ω h) X rA rB
        C.val (pbcSubfieldInclusion l Ω h') rC K)


section GeometricCoefficients
variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The existing continuous precomposition map, at the specified coefficient topology.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedGeometricMap :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l Y E) ⟶ rationalCoefficientSheaf l Z E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1} E) g

/-- Integral precomposition at the same spectral topology.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization). -/
def rationalBalancedIntegralGeometricMap :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (integralCoefficientSheaf l Y E) ⟶ integralCoefficientSheaf l Z E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g

/-- Coefficient postcomposition commutes with geometric precomposition after localization.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: apply the inverse-image adjunction. Both adjuncts take a function f to
x ↦ i(f(pr(x))). Postcomposition commutes with this precomposition on every section.
The adjunction is injective on Hom sets, giving the sheaf equation. -/
theorem rationalBalancedGeometricSquare :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (rationalBalancedCoefficient l E F i Y) ≫ rationalBalancedGeometricMap l F g =
      rationalBalancedGeometricMap l E g ≫ rationalBalancedCoefficient l E F i Z := by
  let := coefficientExtensionNormedField l E
  let := coefficientExtensionNormedField l F
  exact continuousCoefficientPullback_naturality
    (RingHom.ulift i.toRingHom : ULift.{u + 1} E →+* ULift.{u + 1} F)
    (continuous_uliftUp.comp
      ((rationalBalancedEmbedding_continuous l E F i).comp continuous_uliftDown)) g

variable [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

private theorem rationalBalancedFiniteScalarsUnit
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionScalars W d n = Functor.whiskerRight
      (toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
        (pbcLevelConstantComparison W d n).hom.hom)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e := AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)
  have he : Functor.whiskerRight (toSheafify (ProEt.topology W)
        (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
        AdicCoefficients.finiteRingUnit W (ProEtale.PbcQuotient d n) :=
    (AdicCoefficients.finiteRingComparison_exists W
      (ProEtale.PbcQuotient d n)).choose_spec.1.2
  have hconst : toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison W d n).hom.hom =
        AdicCoefficients.constants W (ProEtale.PbcQuotient d n) ≫
          toSheafify (ProEt.topology W)
            (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)) := by
    ext U b
    exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  rw [hconst]
  apply (cancel_mono e.hom.hom).1
  have hi : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg
    (fun f : AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ⟶
      AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ↦ f.hom)
    e.inv_hom_id
  change (ProEtale.finiteCoefficientScalarMap W (ProEtale.PbcQuotient d n) ≫
    e.inv.hom) ≫ e.hom.hom = _
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  rw [Functor.whiskerRight_comp, Category.assoc, he]
  rfl

private theorem rationalBalancedIntegralProjection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
    (s : RationalModuleRealization l E W) (n : ℕ) :
    s.integralIso.hom ≫ continuousCoefficientReduction l E W n =
      pbcAdicProjection W (pbcIntegralDatum l E) n ≫ (s.finiteIso n).hom := by
  apply (cancel_epi s.integralIso.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let _ : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let _ : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  ext V a
  apply ContinuousMap.ext
  intro x
  apply ULift.down_injective
  exact (s.integral_normalization n V a x).symm

private theorem rationalBalancedFiniteComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
    (s : RationalModuleRealization l E W) (n : ℕ) :
    letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        (s.finiteIso n).hom =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
        continuousCoefficientConstantComparison W (finiteCoefficientRing l E n) := by
  let _ : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let _ : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteContinuousCoefficientSheaf l W E n).property
  have hu := rationalBalancedFiniteScalarsUnit (pbcIntegralDatum l E) W n
  ext V a
  apply ContinuousMap.ext
  intro x
  have hn := s.finite_normalization n V a x
  have hunit := congrArg (fun z ↦ (z.app V).hom a) hu
  change _ = _ at hunit
  rw [hunit] at hn
  have hmap := congr_app (toSheafify_naturality (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map (integralCoefficientULift l E n).toCommRingCatIso.hom)) V
  have hmap' := ConcreteCategory.congr_hom hmap a
  have hc := continuousCoefficientConstantComparison_unit W (finiteCoefficientRing l E n)
  have hc' := ConcreteCategory.congr_hom (congr_app hc V)
    (integralCoefficientULift l E n a)
  let e := (integralCoefficientULift l E n).toCommRingCatIso.hom
  let η := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)))
  let η' := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))
  let q := continuousCoefficientConstantComparison W (finiteCoefficientRing l E n)
  let m := sheafifyMap (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).map e)
  change (η'.app V) (e a) = (m.app V) ((η.app V) a) at hmap'
  change (q.hom.app V) ((η'.app V) (e a)) = ContinuousMap.const V.unop.left
    (show finiteCoefficientRing l E n from e a) at hc'
  let f : C(V.unop.left, finiteCoefficientRing l E n) :=
    (s.finiteIso n).hom.hom.app V
      ((pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom.hom.app V
        ((η.app V) a))
  change f x = e a at hn
  let g : C(V.unop.left, finiteCoefficientRing l E n) :=
    q.hom.app V ((m.app V) ((η.app V) a))
  change f x = g x
  rw [hn]
  have hg : g = ContinuousMap.const V.unop.left
      (show finiteCoefficientRing l E n from e a) := by
    change (q.hom.app V) ((m.app V) ((η.app V) a)) = _
    rw [← hmap']
    exact hc'
  exact (congrArg (fun z : C(V.unop.left, finiteCoefficientRing l E n) ↦ z x) hg).symm

/-- The finite-projection completed pullback is exactly continuous precomposition.
Source: BS 6.8.2 (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: under the normalized inverse-limit realizations, reducing the continuous
precomposition map modulo every uniformizer power is the finite-projection map
in completedCoefficientMap. The projections are jointly monic, so the maps agree.
Thus the integral square and its localization are the specified geometric squares. -/
theorem rationalBalancedGeometricNormalization
    (rY : RationalModuleRealization l E Y) (rZ : RationalModuleRealization l E Z) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map rY.integralIso.inv ≫
        completedCoefficientMap g (pbcIntegralDatum l E) ≫ rZ.integralIso.hom =
      rationalBalancedIntegralGeometricMap l E g := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hf (n : ℕ) :
      letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
      letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
      completedFiniteCoefficientMap g (pbcIntegralDatum l E) n ≫ (rZ.finiteIso n).hom =
        L.map (rY.finiteIso n).hom ≫
          continuousCoefficientPullback (finiteCoefficientRing l E n) g := by
    let _ : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let _ : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    apply (cancel_epi
      (L.map (pbcLevelConstantComparison Y (pbcIntegralDatum l E) n).hom)).mp
    change L.map (pbcLevelConstantComparison Y (pbcIntegralDatum l E) n).hom ≫
        (L.map (pbcLevelConstantComparison Y (pbcIntegralDatum l E) n).inv ≫
          proEtaleConstantInverseImageMap g CommRingCat.{u + 1} _ ≫
            (pbcLevelConstantComparison Z (pbcIntegralDatum l E) n).hom) ≫
              (rZ.finiteIso n).hom = _
    simp only [← Category.assoc, ← L.map_comp,
      Iso.hom_inv_id, L.map_id, Category.id_comp]
    rw [Category.assoc, rationalBalancedFiniteComparison l E Z rZ n]
    rw [rationalBalancedFiniteComparison l E Y rY n,
      L.map_comp, Category.assoc, constantComparison_pullback]
    convert congrArg
      (fun z ↦ z ≫ continuousCoefficientConstantComparison Z (finiteCoefficientRing l E n))
      (proEtaleConstantInverseImageMap_naturality g
        (integralCoefficientULift l E n).toCommRingCatIso.hom).symm using 1 <;>
      (simp only [Category.assoc])
    rfl
  have hi : completedCoefficientMap g (pbcIntegralDatum l E) ≫ rZ.integralIso.hom =
      L.map rY.integralIso.hom ≫ rationalBalancedIntegralGeometricMap l E g := by
    apply integralContinuous_hom_ext l E Z
    intro n
    change (_ ≫ rZ.integralIso.hom) ≫ continuousCoefficientReduction l E Z n =
      (L.map rY.integralIso.hom ≫ _) ≫ continuousCoefficientReduction l E Z n
    rw [Category.assoc, rationalBalancedIntegralProjection l E Z rZ n, ← Category.assoc,
      scalarCompletedCoefficientMap_projection]
    rw [Category.assoc, hf n]
    rw [← L.map_comp_assoc, ← rationalBalancedIntegralProjection l E Y rY n, L.map_comp]
    simp only [Category.assoc]
    congr 1
    exact (integralContinuousPullback_reduction l E g n).symm
  change L.map rY.integralIso.inv ≫
    (completedCoefficientMap g (pbcIntegralDatum l E) ≫ rZ.integralIso.hom) = _
  rw [hi, ← Category.assoc, ← L.map_comp, Iso.inv_hom_id, L.map_id, Category.id_comp]
end GeometricCoefficients

/-- The s and t composition comparisons are natural on the entire derived category.
Source: Stacks 0D6D (blueprint: lem-per-rational-scalar-balanced-localization).
Proof: the displayed maps are components of the composition isomorphism between
left adjoints to the same composite restriction functor. The Hom adjunction
bijections are natural on the full derived categories, including inverses of
quasi-isomorphisms. This proves the equation for arbitrary derived morphisms.
The inverse equation follows by composing with the two inverse components. -/
theorem rationalBalancedDerivedNaturality {W : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    {K L : DerivedCategory (pbcModules W R)} (f : K ⟶ L) :
    (pbcDerivedExtend b).map ((pbcDerivedExtend a).map f) ≫
        (pbcReductionNormalization a b c h L).hom =
      (pbcReductionNormalization a b c h K).hom ≫ (pbcDerivedExtend c).map f := by
  let e := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
    (pbcDerivedRestrictComp a b c h)
  have he (M : DerivedCategory (pbcModules W R)) :
      (pbcReductionNormalization a b c h M).hom = e.hom.app M := by
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom,
      pbcReductionTransition, e]
    simp only [Adjunction.leftAdjointCompIso_hom_app,
      Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [he, he]
  exact e.hom.naturality f

private theorem rationalBalancedCancelUnit {C : Type*} [Category C] {A B D : C}
    (σ : A ≅ B) (u : A ≅ D) (v : B ≅ D) (h : σ.hom = u.hom ≫ v.inv) :
    σ.inv ≫ u.hom = v.hom := by
  rw [Iso.inv_comp_eq, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section
attribute [local irreducible] pbcRationalScalarExtension

/-- The multiplication comparison for a literally identity raw scalar functor.
The displayed equality transports only along the literal identity normalization.
Source: BS 6.8.14(2); Stacks 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof: apply rationalBalancedIdentity to A. By definition pbcStageNormalization
at A=A is exactly the published tensor multiplication unit. Conjugate the
identity equation by this normalization; its two inverse unit maps cancel.
The resulting d is still computed by ordinary multiplication on complexes. -/
theorem rationalBalancedNormalizedIdentity
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    (A : Padic.FiniteCoefficientFields l Ω) (rA : RationalModuleRealization l A.val X) :
    ∃ (e : pbcStageTransition l Ω X (le_refl A) = 𝟭 _)
      (o : pbcExtend
        (rationalBalancedCoefficient l A.val A.val (pbcSubfieldInclusion l Ω (le_refl A)) X)
          ≅ 𝟭 _)
      (d : pbcDerivedExtend
        (rationalBalancedCoefficient l A.val A.val (pbcSubfieldInclusion l Ω (le_refl A)) X)
          ≅ 𝟭 _),
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X A.val)) (U : X.ProEtᵒᵖ)
        (a : (rationalCoefficientSheaf l X A.val).obj.obj U) (m : M.val.obj U),
        (o.hom.app M).val.app U
          (pbcTensorSection (rationalBalancedCoefficient l A.val A.val
            (pbcSubfieldInclusion l Ω (le_refl A)) X) M U a m) = a • m) ∧
      (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X A.val)) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (rationalBalancedCoefficient l A.val A.val
            (pbcSubfieldInclusion l Ω (le_refl A)) X) P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P)) ∧
      (∀ K : pbcCoefficientStage l Ω X A,
        ((Functor.isoWhiskerRight (pbcStageNormalization l Ω X (le_refl A)).symm rA.J) ≪≫
            rationalBalancedTheta l A.val A.val (pbcSubfieldInclusion l Ω (le_refl A))
              X rA rA).hom.app K ≫ d.hom.app (rA.J.obj K) =
          rA.J.map (eqToHom (congrArg (fun T ↦ T.obj K) e))) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      classical
      obtain ⟨_, o, d, ho, hd, ht⟩ := rationalBalancedIdentity l A.val X rA
      have e : pbcStageTransition l Ω X (le_refl A) = 𝟭 _ := by
        simp only [pbcStageTransition, ↓reduceDIte]
      refine ⟨e, o, d, ho, hd, ?_⟩
      intro K
      simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        whiskerRight_app, Iso.symm_hom, Category.assoc]
      change rA.J.map ((pbcStageNormalization l Ω X (le_refl A)).inv.app K) ≫
        ((rationalBalancedTheta l A.val A.val (AlgHom.id ℚ_[l] A.val) X rA rA).hom.app K ≫
          d.hom.app (rA.J.obj K)) = _
      erw [ht, ← rA.J.map_comp]
      congr 1
      have hn : (pbcStageNormalization l Ω X (le_refl A)).hom.app K =
          (pbcRationalScalarUnit l A.val X Fact.out Fact.out).hom.app K ≫
            eqToHom (congrArg (fun T ↦ T.obj K) e).symm := by
        simp only [pbcStageNormalization, ↓reduceDIte, Iso.trans_hom, NatTrans.comp_app,
          eqToIso.hom, eqToHom_app]
        change (𝟙 ((pbcRationalScalarExtension l A.val A.val (AlgHom.id ℚ_[l] A.val)
            X Fact.out Fact.out).obj K)) ≫
          ((pbcRationalScalarUnit l A.val X Fact.out Fact.out).hom.app K ≫
            eqToHom (congrArg (fun T ↦ T.obj K) e).symm) = _
        exact Category.id_comp _
      exact rationalBalancedCancelUnit
        ((pbcStageNormalization l Ω X (le_refl A)).app K)
        ((pbcRationalScalarUnit l A.val X Fact.out Fact.out).app K)
        (eqToIso (congrArg (fun T ↦ T.obj K) e)) hn

end

/-- The specified balanced components determine a unique raw natural isomorphism.
The companion statements in this module give its finite-projection and continuous
coefficient normalizations, flat-term K-flat computation, fraction descent, field
tower, pentagon and literal-identity normalizations.
Source: BS 6.8.2 and 6.8.14(2); Stacks 0G7E and 0D6D
(blueprint: lem-per-rational-scalar-balanced-localization).
Proof, following the node's eight steps:
1. Uniqueness of the extended absolute value puts i(t_E) in the target maximal
ideal. Its DVR decomposition u*t_F^e, e ≥ 1, defines the same-index quotient maps.
The inverse-limit universal property gives the normalized integral inclusion.
Taking finite projections proves the square with completedCoefficientMap.
2. The continuous-function realizations identify inclusion with postcomposition
and geometric pullback with precomposition. These commute. Nonzero constant
scalars have their constant reciprocals, so the square localizes unitaly.
3. Choose a flat-term K-flat resolution. Identity-topos coefficient pullback
preserves both properties, by 0G7E, for every intermediate coefficient map.
4. The 0D6D normalized comparisons multiply adjacent scalar factors, with inverse
inserting one. Their universal computation counits identify those formulas on
every representative, independently of resolutions and naturally on derived maps.
5. Compose s with t inverse. Restrict the actual integral scalar extension and use
the recorded realization object and fraction equations. Semilinear localization
extends integral naturality uniquely to the unchanged raw rational objects.
6. If t^r(t^m f-t^n h)=0, multiply its target image by t^(-r-m-n). This proves
equality of fraction images without cancelling t on integral Hom groups.
7. In a tower both flattened routes multiply m tensor l tensor p to ml tensor p.
The specified raw associators are precisely rationalizations of these balanced
comparisons; localization preserves their whiskered natural-transformation equations.
8. For four fields associativity gives nml tensor p on both pentagon routes.
For equal fields the multiplication unitor gives 1x=x=x1. Conjugating by the
published raw tensor normalization makes the equal-field functor literally id.
Existence is rationalBalancedTheta, and equality of all components proves uniqueness. -/
theorem rationalScalarBalancedLocalization :
    ∃! theta : pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J ≅
        sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X),
      ∀ K : PbcRationalDerivedCategory l E X Fact.out Fact.out,
        theta.app K = rationalBalancedComponent l E F i X sE sF K := by
  refine ⟨rationalBalancedTheta l E F i X sE sF, fun _ ↦ rfl, ?_⟩
  intro theta htheta
  apply Iso.ext
  ext K
  exact congrArg Iso.hom (htheta K)

end AlgebraicGeometry.Scheme
