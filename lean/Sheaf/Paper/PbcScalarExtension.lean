/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.Paper.PbcUniformCompleteTriangulated
public import Sheaf.Paper.IntegralTStructure
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.PbcActualScalarPullback
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.Paper.PbcRationalTransport
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage


/-! # Finite scalar extension on the actual proper-base-change categories

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1307,
Milne, Lectures on Etale Cohomology, Section 19.
(blueprint: prop-weil-pbc-scalar-extension)

Coefficient maps are specified on all finite reductions. Integral extension is the
existing universal derived tensor functor. Rational extension is its balanced map
on the actual localized Hom modules, without adjoining retracts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
namespace AlgebraicGeometry.Scheme
section Triangulation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension).
Proof: Project existence of a zero object from pbcRationalTriangulationData. The raw
category is unchanged, so this is exactly the required HasZeroObject proposition. -/
@[instance] theorem pbcScalarRationalZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    HasZeroObject (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) := by
  exact pbcRationalZero l E T Fact.out Fact.out

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcScalarRationalHasShift : HasShift (PbcRationalCategory T (pbcIntegralDatum l E)
  (pbcUniformizer l E)) ℤ :=
  (pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension).
Proof: Project additive shifts from pbcRationalTriangulationData. The preceding
HasShift adapter is its identical chosen shift, and all other class arguments
are propositions, so proof irrelevance identifies their proofs. -/
@[instance] theorem pbcScalarRationalShiftAdditive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    ∀ n : ℤ, (shiftFunctor (PbcRationalCategory T (pbcIntegralDatum l E)
      (pbcUniformizer l E)) n).Additive := by
  exact (pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2.choose

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcScalarRationalLocalizationShift : (ScalarLocalization.localization
  (PbcIntegralRing l E) (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
    (pbcUniformizer l E)).CommShift ℤ :=
  ((pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2
    ).choose_spec.choose

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcScalarRationalPretriangulated : Pretriangulated (PbcRationalCategory T
  (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  ((pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2
    ).choose_spec.choose_spec.2.choose

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension).
Proof: pbcRationalTriangulationData gives TR4 for its chosen raw scalar-localization
pretriangulation. The zero, shift, additive-shift and pretriangulation adapters above
are its identical projections. Thus its IsTriangulated proof has this exact type;
proof irrelevance identifies all propositional class arguments. -/
@[instance] theorem pbcScalarRationalIsTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    IsTriangulated (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) := by
  exact ((pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2
    ).choose_spec.choose_spec.2.choose_spec.1

/-- Expose the existing isomorphism closure of the published integral predicate.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcScalarIntegralIsoClosure :
    ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) :=
  (pbcIntegralUniformComplete_isTriangulated l E T Fact.out Fact.out).1

/-- Expose the existing canonical field action through the geometric Fact hypotheses.
Source: blueprint order 1306 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcScalarRationalLinear :
    Linear E (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  pbcRationalLinear l E T Fact.out Fact.out

end Triangulation
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F)

/-- The given field embedding restricted to the actual lifted valuation rings.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcEmbeddingIntegerMap : PbcIntegralRing l E →+* PbcIntegralRing l F :=
  RingHom.ulift (WeilConjectures.integralScalarIntegerInclusion l E F i)

/-- The same-index positive target quotient kills the source uniformizer ideal power.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the field embedding preserves the extended p-adic absolute value, so it sends
source integers to target integers and the source maximal ideal into the target
maximal ideal. Their uniformizers generate these ideals. Taking the (n+1)-st power
and reducing gives zero, including for ramified extensions. -/
theorem pbcEmbeddingIntegerMap_quotient_kernel (n : ℕ) (a : PbcIntegralRing l E)
    (ha : a ∈ (pbcIntegralDatum l E).ideal ^ (n + 1)) :
    Ideal.Quotient.mk ((pbcIntegralDatum l F).ideal ^ (n + 1))
      (pbcEmbeddingIntegerMap l E F i a) = 0 := by
  have hdown : a.down ∈ Padic.coefficientExtensionIdeal l E (n + 1) := by
    change a ∈ Ideal.span {pbcUniformizer l E} ^ (n + 1) at ha
    change a.down ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ (n + 1)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha ⊢
    obtain ⟨b, hb⟩ := ha
    exact ⟨b.down, congrArg ULift.down hb⟩
  have htarget := Ideal.Quotient.eq_zero_iff_mem.mp
    (WeilConjectures.integralScalar_quotient_kernel l E F i n a.down hdown)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change pbcEmbeddingIntegerMap l E F i a ∈
    Ideal.span {pbcUniformizer l F} ^ (n + 1)
  change WeilConjectures.integralScalarIntegerInclusion l E F i a.down ∈
    Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ (n + 1) at htarget
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at htarget ⊢
  obtain ⟨b, hb⟩ := htarget
  exact ⟨ULift.up b, congrArg ULift.up hb⟩

/-- The finite coefficient map induced by the specified field embedding.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcScalarQuotientMap (n : ℕ) :
    PbcQuotient (pbcIntegralDatum l E) n →+* PbcQuotient (pbcIntegralDatum l F) n :=
  Ideal.Quotient.lift ((pbcIntegralDatum l E).ideal ^ (n + 1))
    ((Ideal.Quotient.mk ((pbcIntegralDatum l F).ideal ^ (n + 1))).comp
      (pbcEmbeddingIntegerMap l E F i))
    (pbcEmbeddingIntegerMap_quotient_kernel l E F i n)

variable (T : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The residue-normalized completed coefficient map exists uniquely.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: postcomposition by the quotient inclusion commutes with each quotient
transition on continuous component functions. Sheafify and compose with the source
limit projections. These maps form a cone over the target coefficient system;
its universal property supplies the unique map with the displayed components. -/
theorem pbcScalarCoefficientMap_exists :
    ∃! a : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
        pbcAdicCompletion T (pbcIntegralDatum l F),
      ∀ n : ℕ, a ≫ pbcAdicProjection T (pbcIntegralDatum l F) n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫
          @AdicCoefficients.coefficientMap T
            (PbcQuotient (pbcIntegralDatum l E) n)
            (PbcQuotient (pbcIntegralDatum l F) n) _ _ _ _
            (pbcScalarQuotientMap l E F i n) := by
  let α : pbcAdicRings T (pbcIntegralDatum l E) ⟶
      pbcAdicRings T (pbcIntegralDatum l F) :=
    NatTrans.ofOpSequence
      (F := pbcAdicRings T (pbcIntegralDatum l E))
      (G := pbcAdicRings T (pbcIntegralDatum l F))
      (fun n ↦ AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n))
      (fun n ↦ by
        have hE : (pbcAdicRings T (pbcIntegralDatum l E)).map
            (homOfLE (n.le_add_right 1)).op = AdicCoefficients.coefficientMap T
              (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l E).ideal (n + 1)) :=
          CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
        have hF : (pbcAdicRings T (pbcIntegralDatum l F)).map
            (homOfLE (n.le_add_right 1)).op = AdicCoefficients.coefficientMap T
              (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l F).ideal (n + 1)) :=
          CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
        rw [hE, hF]
        change AdicCoefficients.coefficientMap T
            (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l E).ideal (n + 1)) ≫
            AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) =
          AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i (n + 1)) ≫
            AdicCoefficients.coefficientMap T
              (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l F).ideal (n + 1))
        have hq : (pbcScalarQuotientMap l E F i n).comp
            (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l E).ideal (n + 1)) =
          (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l F).ideal (n + 1)).comp
            (pbcScalarQuotientMap l E F i (n + 1)) := by
          apply Ideal.Quotient.ringHom_ext
          ext x
          rfl
        have hp : AdicCoefficients.functionPresheafMap T
              (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l E).ideal (n + 1)) ≫
            AdicCoefficients.functionPresheafMap T (pbcScalarQuotientMap l E F i n) =
          AdicCoefficients.functionPresheafMap T (pbcScalarQuotientMap l E F i (n + 1)) ≫
            AdicCoefficients.functionPresheafMap T
              (Ideal.Quotient.factorPowSucc (pbcIntegralDatum l F).ideal (n + 1)) := by
          ext U s
          let : TopologicalSpace
              (PbcQuotient (pbcIntegralDatum l E) (n + 1)) := ⊥
          let : TopologicalSpace (PbcQuotient (pbcIntegralDatum l F) n) := ⊥
          change C(ConnectedComponents U.unop.left,
            PbcQuotient (pbcIntegralDatum l E) (n + 1)) at s
          change (_ : C(ConnectedComponents U.unop.left,
            PbcQuotient (pbcIntegralDatum l F) n)) = _
          apply ContinuousMap.ext
          intro c
          exact DFunLike.congr_fun hq (s c)
        exact ((presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _).symm.trans
          ((congrArg (fun f ↦ (presheafToSheaf (ProEt.topology T)
            CommRingCat.{u + 1}).map f) hp).trans
              ((presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _)))
  refine ⟨limMap α, ?_, ?_⟩
  · intro n
    exact limMap_π α (op n)
  · intro a ha
    apply limit.hom_ext
    intro n
    exact (ha n.unop).trans (limMap_π α n).symm

/-- The actual completed coefficient inclusion, fixed by all residue projections.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcScalarCoefficientMap :
    pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      pbcAdicCompletion T (pbcIntegralDatum l F) :=
  (pbcScalarCoefficientMap_exists l E F i T).exists.choose

/-- Ordinary ambient derived tensor along the actual completed coefficient inclusion.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
abbrev pbcEmbeddingAmbientTensor :
    PbcCompletedDerived T (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived T (pbcIntegralDatum l F) :=
  pbcDerivedExtend (pbcScalarCoefficientMap l E F i T)

variable [IsNoetherian T]
variable (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Ambient tensor preserves the three defining integral membership conditions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: finite-free-completed-scalar-comparison identifies target coefficients as
finite free over source coefficients. Tensor commutes with intrinsic Koszul
completion. By integral-stratified-perfect-characterization, use the same finite
stratification and bounded finite-projective local complexes, extending their
coefficients. Finite-projective splittings survive tensor. The characterization's
reverse implication gives the actual uniform tower and compatible etale origins,
including the quotient cocycles. This uses the constant-completion equivalence and
the canonical coefficient inverse-image identifications, not a different category. -/
theorem pbcEmbeddingAmbientTensor_preserves
    (K : PbcIntegralCategory l E T hDim hInv) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i T).obj K.obj) := by
  sorry

/-- Restriction of the actual ambient tensor, retaining its object and morphism maps.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcEmbeddingIntegralTensor :
    PbcIntegralCategory l E T hDim hInv ⥤ PbcIntegralCategory l F T hDim hInv :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
      pbcEmbeddingAmbientTensor l E F i T)
    (pbcEmbeddingAmbientTensor_preserves l E F i T hDim hInv)

/-- The additive Hom map of rational extension is uniquely fixed on pure tensors.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: integral derived tensor is additive and semilinear for pbcEmbeddingIntegerMap,
by its tensor-section formula and K-flat descent. The displayed formula is balanced
over the source integer ring, so extends uniquely by the tensor universal property.
For ramification t = u v^e, localization at t and v agrees: v inverse is
u v^(e-1) t inverse, and t inverse is u inverse v^(-e). Hence these really are
the source and target raw rational Hom modules. -/
theorem pbcRationalScalarHom_exists (K L : PbcIntegralCategory l E T hDim hInv) :
    ∃! m :
      (ScalarLocalization.mk (R := PbcIntegralRing l E) (p := pbcUniformizer l E) K ⟶
        ScalarLocalization.mk L) →+
      (ScalarLocalization.mk (R := PbcIntegralRing l F) (p := pbcUniformizer l F)
        ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj K) ⟶
          ScalarLocalization.mk ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj L)),
      ∀ (a : Localization.Away (pbcUniformizer l E)) (f : K ⟶ L),
        m (a • (pbcRationalization T (pbcIntegralDatum l E)
          (pbcUniformizer l E)).map f) =
          (pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a))
            • (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
              ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f) := by
  sorry

/-- The unique additive extension of the integral coefficient-change Hom formula.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcRationalScalarHom (K L : PbcIntegralCategory l E T hDim hInv) :=
  (pbcRationalScalarHom_exists l E F i T hDim hInv K L).exists.choose

attribute [-instance] ULift.module in
private theorem pbcRationalScalarHom_tmul (K L : PbcIntegralCategory l E T hDim hInv)
    (a : Localization.Away (pbcUniformizer l E)) (f : K ⟶ L) :
    pbcRationalScalarHom l E F i T hDim hInv K L (a ⊗ₜ[PbcIntegralRing l E] f) =
      (pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a))
        ⊗ₜ[PbcIntegralRing l F] (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f := by
  have h := (pbcRationalScalarHom_exists l E F i T hDim hInv K L).exists.choose_spec a f
  change pbcRationalScalarHom l E F i T hDim hInv K L _ = _ at h
  dsimp only [pbcRationalization, ScalarLocalization.localization] at h
  erw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
  exact h

attribute [-instance] ULift.module in
/-- The specified rational Hom maps preserve identities and composition.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: on pure tensors use multiplication of scalar images, bilinear composition
in ScalarLocalization and functoriality of the actual integral tensor. Additivity
extends the equation to arbitrary sums of pure tensors. -/
theorem pbcRationalScalarHom_laws :
    (∀ K : PbcRationalDerivedCategory l E T hDim hInv,
      pbcRationalScalarHom l E F i T hDim hInv K.obj K.obj (𝟙 K) =
        𝟙 (ScalarLocalization.mk
          ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj K.obj))) ∧
    (∀ (K L M : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) (g : L ⟶ M),
      pbcRationalScalarHom l E F i T hDim hInv K.obj M.obj (f ≫ g) =
        pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f ≫
          pbcRationalScalarHom l E F i T hDim hInv L.obj M.obj g) := by
  constructor
  · intro K
    change pbcRationalScalarHom l E F i T hDim hInv K.obj K.obj
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E] 𝟙 K.obj) = _
    erw [pbcRationalScalarHom_tmul]
    simp only [map_one]
    erw [CategoryTheory.Functor.map_id]
    rfl
  · intro K L M f g
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [map_zero, comp_zero]
      | tmul b g =>
        change pbcRationalScalarHom l E F i T hDim hInv K.obj M.obj
          (ScalarLocalization.composition _ _ _ _ _ _ (b ⊗ₜ[_] g) (a ⊗ₜ[_] f)) =
            ScalarLocalization.composition _ _ _ _ _ _
              (pbcRationalScalarHom l E F i T hDim hInv L.obj M.obj (b ⊗ₜ[_] g))
              (pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj (a ⊗ₜ[_] f))
        erw [ScalarLocalization.composition_tmul, pbcRationalScalarHom_tmul,
          pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul,
          ScalarLocalization.composition_tmul, map_mul, map_mul, map_mul, Functor.map_comp]
      | add g g' hg hg' =>
        erw [Preadditive.comp_add, _root_.map_add, _root_.map_add,
          Preadditive.comp_add]
        exact congrArg₂ (· + ·) hg hg'
    | add f f' hf hf' =>
      erw [Preadditive.add_comp, _root_.map_add, _root_.map_add,
        Preadditive.add_comp]
      exact congrArg₂ (· + ·) hf hf'

/-- Derived scalar extension followed by raw scalar localization, on the actual Dbc.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcRationalScalarExtension :
    PbcRationalDerivedCategory l E T hDim hInv ⥤
      PbcRationalDerivedCategory l F T hDim hInv where
  obj K := ⟨(pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj K.obj⟩
  map {K L} f := pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f
  map_id K := (pbcRationalScalarHom_laws l E F i T hDim hInv).1 K
  map_comp f g := (pbcRationalScalarHom_laws l E F i T hDim hInv).2 _ _ _ f g

end AlgebraicGeometry.Scheme



namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
variable (E F G : Type u) [Field E] [Field F] [Field G]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G]
variable (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G) (T : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed coefficient maps compose as the actual field embeddings do.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: compose with every target finite projection. Both maps send the residue of
an integer x to the residue of j(i(x)). Quotient induction, sheafification and
joint monicity of limit projections give equality. -/
theorem pbcScalarCoefficientMap_comp :
    pbcScalarCoefficientMap l E F i T ≫ pbcScalarCoefficientMap l F G j T =
      pbcScalarCoefficientMap l E G (j.comp i) T := by
  apply (pbcScalarCoefficientMap_exists l E G (j.comp i) T).unique
  · intro n
    have hq : (pbcScalarQuotientMap l F G j n).comp
        (pbcScalarQuotientMap l E F i n) =
          pbcScalarQuotientMap l E G (j.comp i) n := by
      apply Ideal.Quotient.ringHom_ext
      ext x
      rfl
    have hf : AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l F G j n) =
          AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E G (j.comp i) n) := by
      unfold AdicCoefficients.coefficientMap
      rw [← Functor.map_comp]
      congr 1
      exact congrArg (AdicCoefficients.functionPresheafMap T) hq
    unfold pbcScalarCoefficientMap
    rw [Category.assoc,
      (pbcScalarCoefficientMap_exists l F G j T).exists.choose_spec n,
      ← Category.assoc,
      (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n,
      Category.assoc, hf]
  · exact (pbcScalarCoefficientMap_exists l E G (j.comp i) T).exists.choose_spec

/-- The canonical balancing components are natural on derived objects.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the scalar adjunctions defining pbcReductionNormalization have the ordinary
tensor units. Their Hom equivalences are natural, so their balanced adjuncts are
natural. On K-flat representatives the formula is (p tensor s) tensor t to
p tensor st, with its specified inverse. -/
theorem pbcAmbientScalarComp_naturality
    (K L : PbcCompletedDerived T (pbcIntegralDatum l E)) (f : K ⟶ L) :
    (pbcEmbeddingAmbientTensor l F G j T).map
        ((pbcEmbeddingAmbientTensor l E F i T).map f) ≫
      (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
        (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
        (pbcScalarCoefficientMap_comp l E F G i j T) L).hom =
    (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
        (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
        (pbcScalarCoefficientMap_comp l E F G i j T) K).hom ≫
      (pbcEmbeddingAmbientTensor l E G (j.comp i) T).map f := by
  change (pbcEmbeddingAmbientTensor l F G j T).map
      ((pbcEmbeddingAmbientTensor l E F i T).map f) ≫
      pbcReductionNormalizationHom _ _ _ _ L =
    pbcReductionNormalizationHom _ _ _ _ K ≫
      (pbcEmbeddingAmbientTensor l E G (j.comp i) T).map f
  unfold pbcReductionNormalizationHom
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  unfold pbcReductionTransition
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hu :=
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E G (j.comp i) T)).unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  congr 1
  simpa only [Functor.comp_map] using
    ((pbcDerivedRestrictComp (pbcScalarCoefficientMap l E F i T)
    (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
    (pbcScalarCoefficientMap_comp l E F G i j T)).inv.naturality
      ((pbcEmbeddingAmbientTensor l E G (j.comp i) T).map f))

/-- The ambient associator is the adjunction-normalized balanced tensor comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcAmbientScalarComp :
    pbcEmbeddingAmbientTensor l E F i T ⋙ pbcEmbeddingAmbientTensor l F G j T ≅
      pbcEmbeddingAmbientTensor l E G (j.comp i) T :=
  NatIso.ofComponents
    (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
      (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
      (pbcScalarCoefficientMap_comp l E F G i j T))
    (fun f ↦ pbcAmbientScalarComp_naturality l E F G i j T _ _ f)

variable [IsNoetherian T] (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Rational balancing is the image of the specified ambient balanced comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible]
def pbcRationalScalarCompComponent (K : PbcRationalDerivedCategory l E T hDim hInv) :
    (pbcRationalScalarExtension l F G j T hDim hInv).obj
        ((pbcRationalScalarExtension l E F i T hDim hInv).obj K) ≅
      (pbcRationalScalarExtension l E G (j.comp i) T hDim hInv).obj K :=
  (pbcRationalization T (pbcIntegralDatum l G) (pbcUniformizer l G)).mapIso
    (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l G))
      ((pbcAmbientScalarComp l E F G i j T).app K.obj.obj))

attribute [-instance] ULift.module in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual localized balancing components are natural on all rational morphisms.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: ambient balancing is natural on integral maps. The scalar Hom formula
intertwines both sides on every pure tensor; the coefficient inclusions compose.
The two additive sides therefore agree on every localized morphism. -/
theorem pbcRationalScalarComp_naturality
    (K L : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) :
    (pbcRationalScalarExtension l F G j T hDim hInv).map
        ((pbcRationalScalarExtension l E F i T hDim hInv).map f) ≫
      (pbcRationalScalarCompComponent l E F G i j T hDim hInv L).hom =
    (pbcRationalScalarCompComponent l E F G i j T hDim hInv K).hom ≫
      (pbcRationalScalarExtension l E G (j.comp i) T hDim hInv).map f := by
  change pbcRationalScalarHom l F G j T hDim hInv _ _
      (pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f) ≫ _ =
    _ ≫ pbcRationalScalarHom l E G (j.comp i) T hDim hInv K.obj L.obj f
  induction f using TensorProduct.induction_on with
  | zero =>
    erw [map_zero, map_zero, map_zero, zero_comp, comp_zero]
  | tmul a f =>
    erw [pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul,
      pbcRationalScalarHom_tmul]
    simp only [RingEquiv.apply_symm_apply, AlgHom.comp_apply]
    unfold pbcRationalScalarCompComponent
    change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (_ ⊗ₜ[_] _) =
      ScalarLocalization.composition _ _ _ _ _ _ (_ ⊗ₜ[_] _) (1 ⊗ₜ[_] _)
    erw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one]
    congr 1
    apply ObjectProperty.hom_ext
    exact (pbcAmbientScalarComp l E F G i j T).hom.naturality f.hom
  | add f g hf hg =>
    simp only [_root_.map_add]
    erw [Preadditive.add_comp, Preadditive.comp_add]
    exact congrArg₂ (· + ·) hf hg

/-- The specified natural rational associator before literal-unit normalization.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcRationalScalarComp :
    pbcRationalScalarExtension l E F i T hDim hInv ⋙
        pbcRationalScalarExtension l F G j T hDim hInv ≅
      pbcRationalScalarExtension l E G (j.comp i) T hDim hInv :=
  NatIso.ofComponents (pbcRationalScalarCompComponent l E F G i j T hDim hInv)
    (fun f ↦ pbcRationalScalarComp_naturality l E F G i j T hDim hInv _ _ f)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section Units
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Identity scalar restriction is fixed by identity functions on sections.
Source: Stacks 03DA (blueprint: prop-weil-pbc-scalar-extension).
Proof: restriction along the identity changes no module action. The identity
functions are linear and natural. Their components determine the isomorphism. -/
theorem pbcScalarRestrictId_exists :
    ∃! e : pbcRestrict (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))) ≅ 𝟭 _,
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
        (U : T.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  refine ⟨Iso.refl _, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e he
    apply Iso.ext
    ext M U x
    exact he M U x

/-- The ordinary identity-on-sections restriction comparison.
Source: Stacks 03DA (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarRestrictId := (pbcScalarRestrictId_exists l E T).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity completed coefficient map fixes all finite projections.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the identity field embedding induces the identity on each quotient, hence
on each quotient coefficient sheaf. Limit projections are jointly monic. -/
theorem pbcScalarCoefficientMap_id :
    pbcScalarCoefficientMap l E E (AlgHom.id (Padic l) E) T =
      𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E)) := by
  apply (pbcScalarCoefficientMap_exists l E E (AlgHom.id (Padic l) E) T).unique
  · exact (pbcScalarCoefficientMap_exists l E E (AlgHom.id (Padic l) E) T).exists.choose_spec
  intro n
  have hq : pbcScalarQuotientMap l E E (AlgHom.id (Padic l) E) n = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  rw [hq]
  have hp : AdicCoefficients.functionPresheafMap T
      (RingHom.id (PbcQuotient (pbcIntegralDatum l E) n)) = 𝟙 _ := by
    ext U s
    rfl
  simp only [AdicCoefficients.coefficientMap, hp, Category.id_comp]
  rw [(presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id]
  exact (Category.comp_id _).symm

/-- The canonical tensor unit is conjugate to identity restriction under the
ordinary-unit-normalized derived adjunction.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcEmbeddingAmbientUnit :
    pbcEmbeddingAmbientTensor l E E (AlgHom.id (Padic l) E) T ≅ 𝟭 _ :=
  eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (pbcScalarCoefficientMap_id l E T)) ≪≫
    ((conjugateIsoEquiv
      (pbcDerivedScalarAdjunction (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))))
      (Adjunction.id : (𝟭 (PbcCompletedDerived T (pbcIntegralDatum l E))) ⊣ 𝟭 _)).symm
        (Functor.mapDerivedCategoryNatIso (pbcScalarRestrictId l E T) ≪≫
          Functor.mapDerivedCategoryIdIso _)).symm

variable [IsNoetherian T]
variable (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Rational tensor unit components are localizations of the ambient tensor units.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible]
def pbcRationalScalarUnitComponent (K : PbcRationalDerivedCategory l E T hDim hInv) :
    (pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv).obj K ≅ K :=
  (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).mapIso
    (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
      ((pbcEmbeddingAmbientUnit l E T).app K.obj.obj))

attribute [-instance] ULift.module in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified unit components are natural on every localized Hom module.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: on a pure tensor this is naturality of the ambient unit and the rational
Hom formula. Additivity extends it to sums of pure tensors. -/
theorem pbcRationalScalarUnit_naturality
    (K L : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) :
    (pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv).map f ≫
        (pbcRationalScalarUnitComponent l E T hDim hInv L).hom =
      (pbcRationalScalarUnitComponent l E T hDim hInv K).hom ≫ f := by
  change pbcRationalScalarHom l E E (AlgHom.id (Padic l) E) T hDim hInv
    K.obj L.obj f ≫ _ = _
  induction f using TensorProduct.induction_on with
  | zero => erw [map_zero, zero_comp, comp_zero]
  | tmul a f =>
    erw [pbcRationalScalarHom_tmul]
    simp only [AlgHom.id_apply, RingEquiv.symm_apply_apply]
    unfold pbcRationalScalarUnitComponent
    change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (a ⊗ₜ[_] _) =
      ScalarLocalization.composition _ _ _ _ _ _ (a ⊗ₜ[_] f) (1 ⊗ₜ[_] _)
    erw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one]
    congr 1
    apply ObjectProperty.hom_ext
    exact (pbcEmbeddingAmbientUnit l E T).hom.naturality f.hom
  | add f g hf hg =>
    erw [_root_.map_add, Preadditive.add_comp, Preadditive.comp_add]
    exact congrArg₂ (· + ·) hf hg

/-- The natural rational tensor unit, before choosing literal identity transitions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcRationalScalarUnit :
    pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv ≅ 𝟭 _ :=
  NatIso.ofComponents (pbcRationalScalarUnitComponent l E T hDim hInv)
    (fun f ↦ pbcRationalScalarUnit_naturality l E T hDim hInv _ _ f)
end Units
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section ScalarShift
variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) (T : Scheme.{u})

private theorem pbcPostShiftKan
    {D : Type*} [Category* D]
    {D' : Type*} [Category* D'] [HasShift D' ℤ]
    {L : Type*} [Category* L]
    (F : D ⥤ D') (Q : D ⥤ L)
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    (LF ⋙ shiftFunctor D' n).IsRightKanExtension
      ((associator Q LF (shiftFunctor D' n)).inv ≫ whiskerRight α (shiftFunctor D' n)) := by
  let P := RightExtension.postcompose₂ Q F (shiftFunctor D' n)
  let : IsIso (𝟙 (F ⋙ shiftFunctor D' n)) := by infer_instance
  let : P.IsEquivalence := by
    dsimp [P, RightExtension.postcompose₂]
    let t : ((whiskeringRight L D' D').obj (shiftFunctor D' n)) ⋙
        (whiskeringLeft D L D').obj Q ⟶
        (whiskeringLeft D L D').obj Q ⋙
          ((whiskeringRight D D' D').obj (shiftFunctor D' n)) :=
      { app G := (associator Q G (shiftFunctor D' n)).inv }
    let : IsIso t := by
      apply NatIso.isIso_of_isIso_app
    exact CostructuredArrow.isEquivalenceMap₂ t (𝟙 _)
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n) α

set_option linter.unusedVariables false in
private theorem pbcKanShift_unique
    {D : Type*} [Category* D] [HasShift D ℤ]
    {D' : Type*} [Category* D'] [HasShift D' ℤ]
    {L : Type*} [Category* L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) (hLF : LF.IsRightKanExtension α) :
    ∃! q : LF.CommShift ℤ,
      (fun [qInst : LF.CommShift ℤ] ↦ NatTrans.CommShift α ℤ) (qInst := q) := by
  obtain ⟨q, hq⟩ := rightKanExtension_coherentShift F Q LF α hLF
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have hi (n : ℤ) : q'.1 n = q.1 n := by
    apply Iso.ext
    let γ := (associator Q LF (shiftFunctor D' n)).inv ≫
      whiskerRight α (shiftFunctor D' n)
    let : LF.IsRightKanExtension α := hLF
    let : (LF ⋙ shiftFunctor D' n).IsRightKanExtension γ := pbcPostShiftKan F Q LF α n
    apply (LF ⋙ shiftFunctor D' n).hom_ext_of_isRightKanExtension γ
    ext X
    have h₁ := NatTrans.congr_app (hq'.1 n) X
    have h₂ := NatTrans.congr_app (hq.1 n) X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app] at h₁ h₂
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app X))).mp
    simpa only [γ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_inv_app, Category.id_comp, Category.assoc] using h₁.trans h₂.symm
  have hh := funext hi
  rcases q' with ⟨c, z, a⟩
  change c = q.1 at hh
  cases hh
  rfl

set_option linter.unusedVariables false in
/-- Universal tensor counits uniquely fix the termwise derived shift comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: ordinary tensor commutes with cochain shifts, with the identity map on
shifted tensor terms. Its homotopy functor therefore has that comparison.
On flat-term K-flat representatives the universal counit is invertible, so this
comparison descends uniquely and satisfies zero and addition coherence. -/
theorem pbcAmbientScalarShift_exists :
    ∃! q : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ,
      (fun [qInst : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ] ↦
        NatTrans.CommShift (pbcExtensionCounit (pbcScalarCoefficientMap l E F i T)) ℤ)
          (qInst := q) := by
  let φ := pbcScalarCoefficientMap l E F i T
  have h := pbcDerivedExtension_universal φ
  have hKan := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
        (.up ℤ))
  exact pbcKanShift_unique _ DerivedCategory.Qh (pbcDerivedExtend φ)
    (pbcExtensionCounit φ) hKan

/-- The tensor shift comparison normalized by its actual derived counit.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcAmbientScalarShift : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ :=
  (pbcAmbientScalarShift_exists l E F i T).exists.choose

universe u₁ v₁ w₁ u₂ v₂ w₂

private theorem pbcExactOfCounit
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (F : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory B)
    [F.CommShift ℤ] [F.IsTriangulated]
    (LF : DerivedCategory A ⥤ DerivedCategory B) [LF.CommShift ℤ]
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F)
    (hKan : LF.IsRightKanExtension ε) (hε : NatTrans.CommShift ε ℤ)
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        IsIso (ε.app Y) ∧ HomotopyCategory.quasiIso A (.up ℤ) s) :
    LF.IsTriangulated := by
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hW : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hleft, hright⟩, fun _ _ _ _ h g f ↦ hsat _ _ _ _ g h f⟩, htri⟩
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦ IsIso (ε.app X)
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → W s → IsIso (F.map s) := by
    intro X Y s hX hY hs
    let : IsIso (ε.app X) := hX
    let : IsIso (ε.app Y) := hY
    have hqs : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh W s hs
    let := hqs
    have hn := ε.naturality s
    dsimp only [Functor.comp_map] at hn
    have he : F.map s = CategoryTheory.inv (ε.app X) ≫ LF.map (DerivedCategory.Qh.map s) ≫
        ε.app Y := by
      rw [hn, IsIso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  have hdefined : ∀ X, F.IsTriangulatedLeftDerivedDefinedAt W hW X := by
    intro X
    obtain ⟨Y, _, hc, _, _⟩ :=
      resolvingClass_essentialConstancy W F P hres hinv X
    exact ⟨Y, hc⟩
  have hsource : (DerivedCategory.Qh ⋙ LF).IsTriangulated :=
    ⟨fun K hK ↦ leftDerived_kan_map_source_distinguished
      (HomotopyCategory A (.up ℤ)) (DerivedCategory B) (DerivedCategory A)
      F W hW DerivedCategory.Qh LF ε hKan hdefined hε K hK⟩
  let := hsource
  have := Localization.essSurj_mapArrow DerivedCategory.Qh W
  exact Functor.isTriangulated_of_precomp DerivedCategory.Qh LF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientTensorExact :
    (pbcEmbeddingAmbientTensor l E F i T).IsTriangulated := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let φ := pbcScalarCoefficientMap l E F i T
  let A := pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))
  let B := pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l F))
  let F₀ := (pbcExtend φ).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh.{u + 2} (C := B)
  have hUniversal := pbcDerivedExtension_universal φ
  have hKan := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)
      (HomotopyCategory.quasiIso A (.up ℤ))
  have hε : NatTrans.CommShift (pbcExtensionCounit φ) ℤ :=
    (pbcAmbientScalarShift_exists l E F i T).exists.choose_spec
  apply pbcExactOfCounit.{u + 2, u + 1, u + 2, u + 2, u + 1, u + 2}
    F₀ (pbcDerivedExtend φ) (pbcExtensionCounit φ) hKan hε
  intro K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, f, hL, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := pbcAdicCompletion T (pbcIntegralDatum l E)) K
  refine ⟨(HomotopyCategory.quotient A (.up ℤ)).obj L,
    (HomotopyCategory.quotient A (.up ℤ)).map f,
    pbcExtensionCounit_isIso φ L hL, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf


variable [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The integral restriction retains the actual ambient functor through its inclusion.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcIntegralScalarInclusionIso :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F)) ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
        pbcEmbeddingAmbientTensor l E F i T := Iso.refl _

private theorem pbcIntegralShift_unique
    {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [G.CommShift ℤ] [H.CommShift ℤ] [G.Full] [G.Faithful]
    (e : F ⋙ G ≅ H) (q r : F.CommShift ℤ)
    (hq : letI := q; NatTrans.CommShift e.hom ℤ)
    (hr : letI := r; NatTrans.CommShift e.hom ℤ) : q = r := by
  have hi : q.commShiftIso = r.commShiftIso := by
    funext n
    apply Iso.ext
    ext X
    apply G.map_injective
    have hq' := @NatTrans.shift_app_comm _ _ _ _ (F ⋙ G) H e.hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ F G ℤ _ _ _ _ q inferInstance)
      inferInstance hq n X
    have hr' := @NatTrans.shift_app_comm _ _ _ _ (F ⋙ G) H e.hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ F G ℤ _ _ _ _ r inferInstance)
      inferInstance hr n X
    simp only [Functor.commShiftIso_comp_hom_app] at hq' hr'
    exact (cancel_mono _).mp ((cancel_mono _).mp (hq'.trans hr'.symm))
  cases q
  cases r
  cases hi
  rfl

set_option linter.unusedVariables false in
/-- Faithful full inclusions uniquely transport the ambient tensor shift.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: conjugate the ambient comparison by the inherited inclusion's shift
comparisons. Fullness lifts it to the integral subcategory; faithfulness lifts
its inverse, naturality and zero/addition coherence. Faithfulness also proves
uniqueness, with the stated commuting inclusion equation. -/
theorem pbcIntegralScalarShift_exists :
    ∃! q : (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ,
      (fun [qInst : (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ] ↦
        NatTrans.CommShift (pbcIntegralScalarInclusionIso l E F i T).hom ℤ) (qInst := q) := by
  let q := Functor.CommShift.ofComp (pbcIntegralScalarInclusionIso l E F i T) ℤ
  have hq : letI := q
      NatTrans.CommShift (pbcIntegralScalarInclusionIso l E F i T).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (pbcIntegralScalarInclusionIso l E F i T) ℤ
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact pbcIntegralShift_unique (pbcIntegralScalarInclusionIso l E F i T) r q hr hq

/-- The inherited integral shift, fixed by the ambient inclusion equation.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcIntegralScalarShift :
    (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ :=
  (pbcIntegralScalarShift_exists l E F i T).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor Hom formula agrees with tensoring integral arrows by one.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: put the scalar equal to one in pbcRationalScalarHom_exists. The normalized
coefficient isomorphisms and the algebra inclusion send one to one, yielding the
displayed naturality equation of identity components. -/
theorem pbcScalarLocalization_naturality
    {K L : PbcIntegralCategory l E T dim.out inv.out} (f : K ⟶ L) :
    (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (pbcRationalScalarExtension l E F i T dim.out inv.out).map
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) := by
  have h := (pbcRationalScalarHom_exists l E F i T dim.out inv.out K L).exists.choose_spec
    (1 : Localization.Away (pbcUniformizer l E)) f
  simpa only [pbcRationalScalarExtension, pbcRationalScalarHom, one_smul, map_one,
    Category.comp_id, Category.id_comp, pbcRationalization,
    ScalarLocalization.localization, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h.symm

/-- The integral-to-rational tensor square has identity components on objects.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarLocalizationIso :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F) ≅
      pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i T dim.out inv.out :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ pbcScalarLocalization_naturality l E F i T f)

universe r v

private noncomputable def pbcRawComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm


private theorem pbcRawIsLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (ScalarLocalization.localization R C p).IsLocalization
      (Rationalization.W (Submonoid.powers p) C) := by
  let M := Submonoid.powers p
  let E := pbcRawComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, ScalarLocalization.localization, pbcRawComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

private theorem pbcPreShiftUnique
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W] [Q.CommShift ℤ]
    (H : C ⥤ E) [H.CommShift ℤ] (F : D ⥤ E) (e : Q ⋙ F ≅ H)
    (q r : F.CommShift ℤ)
    (hq : letI := q; NatTrans.CommShift e.hom ℤ)
    (hr : letI := r; NatTrans.CommShift e.hom ℤ) : q = r := by
  have hi : q.commShiftIso = r.commShiftIso := by
    funext n
    apply Iso.ext
    apply Localization.natTrans_ext Q W
    intro X
    have hq' := @NatTrans.shift_app_comm _ _ _ _ (Q ⋙ F) H e.hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ Q F ℤ _ _ _ _ inferInstance q)
      inferInstance hq n X
    have hr' := @NatTrans.shift_app_comm _ _ _ _ (Q ⋙ F) H e.hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ Q F ℤ _ _ _ _ inferInstance r)
      inferInstance hr n X
    simp only [Functor.commShiftIso_comp_hom_app] at hq' hr'
    exact (cancel_epi _).mp ((cancel_mono _).mp (hq'.trans hr'.symm))
  cases q
  cases r
  cases hi
  rfl


set_option linter.unusedVariables false in
/-- The rational shift comparison is precisely the localized ambient tensor comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the inherited integral shift changes no underlying completed complex. On
pure tensor Hom modules localization extends the ambient shift comparison. The
balancing formula makes it natural for all rational morphisms. The ambient zero
and addition coherence descend, and generation by pure tensors gives uniqueness. -/
theorem pbcRationalScalarShift_exists :
    ∃! q : (pbcRationalScalarExtension l E F i T dim.out inv.out).CommShift ℤ,
      (fun [qInst : (pbcRationalScalarExtension l E F i T dim.out inv.out).CommShift ℤ] ↦
        NatTrans.CommShift (pbcScalarLocalizationIso l E F i T).hom ℤ) (qInst := q) := by
  let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let W := Rationalization.W (Submonoid.powers (pbcUniformizer l E))
    (PbcIntegralCategory l E T dim.out inv.out)
  let H := pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
    pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)
  let F' := pbcRationalScalarExtension l E F i T dim.out inv.out
  let e : Q ⋙ F' ≅ H := (pbcScalarLocalizationIso l E F i T).symm
  let : Q.IsLocalization W :=
    pbcRawIsLocalization (PbcIntegralRing l E)
      (PbcIntegralCategory l E T dim.out inv.out) (pbcUniformizer l E)
  let : Localization.Lifting Q W H F' := ⟨e⟩
  let q := Functor.commShiftOfLocalization Q W ℤ H F'
  have hq : letI := q; NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q W ℤ H F'
  refine ⟨q, ?_, ?_⟩
  · let := q
    let : NatTrans.CommShift e.hom ℤ := hq
    exact NatTrans.CommShift.of_iso_inv e ℤ
  · intro r hr
    have hr' : letI := r; NatTrans.CommShift e.hom ℤ := by
      let := r
      let : NatTrans.CommShift (pbcScalarLocalizationIso l E F i T).hom ℤ := hr
      exact NatTrans.CommShift.of_iso_inv (pbcScalarLocalizationIso l E F i T) ℤ
    exact pbcPreShiftUnique Q W H F' e r q hr' hq

/-- The canonical rational tensor shift with its integral normalization retained.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcRationalScalarShift :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).CommShift ℤ :=
  (pbcRationalScalarShift_exists l E F i T).exists.choose

/-- The actual raw rational tensor functor is additive and triangulated.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: ambient derived tensor preserves the termwise cone differential and its
canonical shift. Its integral restriction preserves inherited triangles because
it preserves the actual uniform complete property. Every raw rational triangle
is isomorphic to an integral image triangle. The scalar Hom formula sends that
image to the integral tensor image. It therefore preserves distinguished triangles
with the normalized last arrow; additivity follows on the tensor Hom generators. -/
theorem pbcRationalScalarExact :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).Additive ∧
      (pbcRationalScalarExtension l E F i T dim.out inv.out).IsTriangulated := by
  have hAdd : (pbcRationalScalarExtension l E F i T dim.out inv.out).Additive :=
    ⟨fun {K L} f g ↦ (pbcRationalScalarHom l E F i T dim.out inv.out K.obj L.obj).map_add f g⟩
  refine ⟨hAdd, ?_⟩
  have hAmbient := pbcAmbientTensorExact l E F i T
  let := hAmbient
  have hInc : NatTrans.CommShift (pbcIntegralScalarInclusionIso l E F i T).hom ℤ :=
    (pbcIntegralScalarShift_exists l E F i T).exists.choose_spec
  let := hInc
  have hIntegral :
      (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right
      (pbcIntegralScalarInclusionIso l E F i T)).2 inferInstance
  let := hIntegral
  let QE := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let QF := pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)
  let W := Rationalization.W (Submonoid.powers (pbcUniformizer l E))
    (PbcIntegralCategory l E T dim.out inv.out)
  let : QE.IsLocalization W := pbcRawIsLocalization (PbcIntegralRing l E)
    (PbcIntegralCategory l E T dim.out inv.out) (pbcUniformizer l E)
  have hQE : QE.IsTriangulated :=
    ((pbcRationalTriangulationData l E T dim.out inv.out).choose_spec.choose_spec.2
      ).choose_spec.choose_spec.2.choose_spec.2.1
  have hQF : QF.IsTriangulated :=
    ((pbcRationalTriangulationData l F T dim.out inv.out).choose_spec.choose_spec.2
      ).choose_spec.choose_spec.2.choose_spec.2.1
  let := hQE
  let := hQF
  have := Localization.essSurj_mapArrow QE W
  have hIso : NatTrans.CommShift (pbcScalarLocalizationIso l E F i T).hom ℤ :=
    (pbcRationalScalarShift_exists l E F i T).exists.choose_spec
  let := hIso
  exact Functor.isTriangulated_of_precomp_iso (pbcScalarLocalizationIso l E F i T).symm

/-- Additivity from the actual rational Hom formula.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcRationalScalarAdditive :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).Additive :=
  (pbcRationalScalarExact l E F i T).1

/-- Exactness with the normalized tensor shift.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcRationalScalarTriangulated :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).IsTriangulated :=
  (pbcRationalScalarExact l E F i T).2
end ScalarShift
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section NestedFields
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The actual finite subfields, in a common ambient field; no algebraic closure
hypothesis is needed for this finite tower. Source: blueprint order 1307
(blueprint: prop-weil-pbc-scalar-extension). -/
abbrev pbcCoefficientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalDerivedCategory l E.val T dim.out inv.out

/-- A nested finite subfield inclusion, with its actual algebra homomorphism.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcSubfieldInclusion {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    E.val →ₐ[Padic l] F.val := IntermediateField.inclusion h

/-- Identity inclusions are the actual algebra identity.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: both maps fix every element of the subfield. -/
theorem pbcSubfieldInclusion_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcSubfieldInclusion l Ω (le_refl E) = AlgHom.id (Padic l) E.val := by
  ext x
  rfl

/-- Actual inclusions compose as direct inclusions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: both maps send each subfield element to its same ambient scalar. -/
theorem pbcSubfieldInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    (pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h) =
      pbcSubfieldInclusion l Ω (h.trans h') := by
  ext x
  rfl

/-- The actual rational tensor before literal identity normalization.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
abbrev pbcStageRaw {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F :=
  pbcRationalScalarExtension l E.val F.val (pbcSubfieldInclusion l Ω h) T dim.out inv.out

/-- Equal coefficient fields use the literal identity functor.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcStageTransition {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F := by
  classical
  exact if e : E = F then e ▸ 𝟭 (pbcCoefficientStage l Ω T E)
    else pbcStageRaw l Ω T h

/-- Normalization uses precisely the ordinary tensor multiplication unit.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcStageNormalization {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcStageRaw l Ω T h ≅ pbcStageTransition l Ω T h := by
  classical
  by_cases e : E = F
  · subst F
    exact eqToIso (congrArg
      (fun i ↦ pbcRationalScalarExtension l E.val E.val i T dim.out inv.out)
      (pbcSubfieldInclusion_id l Ω E)) ≪≫
        pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
          eqToIso (by unfold pbcStageTransition; rw [dif_pos rfl])
  · exact eqToIso (by simp only [pbcStageTransition, dif_neg e])

/-- Balancing, conjugated by the specified tensor units, is the chosen associator.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcStageAssociator {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    pbcStageTransition l Ω T h ⋙ pbcStageTransition l Ω T h' ≅
      pbcStageTransition l Ω T (h.trans h') :=
  isoWhiskerRight (pbcStageNormalization l Ω T h).symm _ ≪≫
    isoWhiskerLeft _ (pbcStageNormalization l Ω T h').symm ≪≫
    pbcRationalScalarComp l E.val F.val G.val
      (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out ≪≫
    eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (pbcSubfieldInclusion_comp l Ω h h')) ≪≫
    pbcStageNormalization l Ω T (h.trans h')

/-- Normalized tensor balancing satisfies both units and the four-field pentagon.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: on a K-flat complex both paths send the three nested scalar factors to
their product, with the same remaining tensor factor. Associativity gives equality
before localization. Multiplication by one gives each unit equation. The two
localizations preserve these equations, including coincident adjacent fields. -/
theorem pbcStageAssociator_laws :
    (∀ {E F G H : Padic.FiniteCoefficientFields l Ω}
      (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H)
      (K : pbcCoefficientStage l Ω T E),
      (pbcStageTransition l Ω T h'').map
          ((pbcStageAssociator l Ω T h h').hom.app K) ≫
        (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
      (pbcStageAssociator l Ω T h' h'').hom.app
          ((pbcStageTransition l Ω T h).obj K) ≫
        (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcStageTransition l Ω T (le_refl E) = 𝟭 _) ∧
    (∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
      HEq (pbcStageAssociator l Ω T (le_refl E) h)
        (Functor.leftUnitor (pbcStageTransition l Ω T h)) ∧
      HEq (pbcStageAssociator l Ω T h (le_refl F))
        (Functor.rightUnitor (pbcStageTransition l Ω T h))) := by
  sorry

/-- Normalized transitions retain the canonical tensor shift comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcStageTransitionShift {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (pbcStageTransition l Ω T h).CommShift ℤ :=
  Functor.CommShift.ofIso (pbcStageNormalization l Ω T h) ℤ

/-- Literal normalization preserves addition and exactness with this shift.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: conjugating by the specified natural tensor-unit isomorphism preserves
addition and distinguished image triangles. Its transported shift is the one
just defined, so the triangle's last arrow is retained. -/
theorem pbcStageExact {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (pbcStageTransition l Ω T h).Additive ∧
      (pbcStageTransition l Ω T h).IsTriangulated := by
  constructor
  · exact Functor.additive_of_iso (pbcStageNormalization l Ω T h)
  · have : NatTrans.CommShift (pbcStageNormalization l Ω T h).hom ℤ :=
      Functor.CommShift.ofIso_compatibility (pbcStageNormalization l Ω T h) ℤ
    exact Functor.isTriangulated_of_iso (pbcStageNormalization l Ω T h)

/-- The specified associators commute with every integer shift.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: balancing is multiplication on shifted tensor terms, with the same signs
on both sides. Universal derived counits and rational tensor generation descend
the equation. Conjugation by the tensor units preserves it. -/
theorem pbcStageAssociatorShift {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    NatTrans.CommShift (pbcStageAssociator l Ω T h h').hom ℤ := by
  sorry
end NestedFields
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section AmbientOperations

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Finite-free coefficient extension preserves ambient intrinsic completeness.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: finite-free-completed-scalar-comparison realizes tensor as a finite sum.
Finite sums commute with the Koszul completion tower and its derived limit. In
the target ring the two uniformizers define cofinal filtrations, since the source
uniformizer is a unit times a positive power of the target uniformizer. The two
completion reflectors and their units therefore agree. Tensoring an invertible
source completion unit gives an invertible target completion unit. -/
theorem pbcScalarPreservesComplete (W : Scheme.{u})
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcLevelConstantComparison_eq (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcLevelScalar_naturality (T : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (d : AdicCoefficientDatum A) (e : AdicCoefficientDatum B)
    (n : ℕ) (φ : PbcQuotient d n →+* PbcQuotient e n) :
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ) ≫
      (pbcLevelConstantComparison T e n).hom =
    (pbcLevelConstantComparison T d n).hom ≫ AdicCoefficients.coefficientMap T φ := by
  rw [pbcLevelConstantComparison_eq, pbcLevelConstantComparison_eq]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫ (presheafToSheaf _ CommRingCat).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarFiniteStructureSquare {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (d : AdicCoefficientDatum A) (e : AdicCoefficientDatum B)
    (n : ℕ) (φ : PbcQuotient d n →+* PbcQuotient e n) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (AdicCoefficients.coefficientMap Y φ) ≫ completedFiniteCoefficientMap g e n =
      completedFiniteCoefficientMap g d n ≫ AdicCoefficients.coefficientMap X φ := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hY : AdicCoefficients.coefficientMap Y φ ≫
      (pbcLevelConstantComparison Y e n).inv =
    (pbcLevelConstantComparison Y d n).inv ≫
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ) := by
    rw [← cancel_epi (pbcLevelConstantComparison Y d n).hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← pbcLevelScalar_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  unfold completedFiniteCoefficientMap
  change L.map _ ≫ L.map _ ≫ _ ≫ _ = L.map _ ≫ _ ≫ _ ≫ _
  rw [← L.map_comp_assoc, hY, L.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc]
  erw [proEtaleConstantInverseImageMap_naturality g (CommRingCat.ofHom φ)]
  rw [Category.assoc, pbcLevelScalar_naturality]
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual completed coefficient inclusion commutes with the ringed structure map.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: apply every finite target projection. Both paths take a continuous residue
function, postcompose with the specified field inclusion and precompose with the
base-change map on connected components. Those operations commute. Joint monicity
of all coefficient limit projections gives the displayed completed equality. -/
theorem pbcScalarCoefficientStructureSquare :
    pbcActualCoefficientRingMap Y (pbcScalarCoefficientMap l E F i Y) ≫
        pbcActualStructureMap g (pbcIntegralDatum l F) =
      pbcActualStructureMap g (pbcIntegralDatum l E) ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map
          (pbcActualCoefficientRingMap X (pbcScalarCoefficientMap l E F i X)) := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let D := proEtaleSheafDirectImage g CommRingCat.{u + 1}
  have hp {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
      completedCoefficientMap g d ≫ pbcAdicProjection X d n =
        L.map (pbcAdicProjection Y d n) ≫ completedFiniteCoefficientMap g d n :=
    limit.lift_π _ (op n)
  have hc : L.map (pbcScalarCoefficientMap l E F i Y) ≫
      completedCoefficientMap g (pbcIntegralDatum l F) =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫
      pbcScalarCoefficientMap l E F i X := by
    apply limit.hom_ext
    intro n
    change _ ≫ pbcAdicProjection X (pbcIntegralDatum l F) n.unop =
      _ ≫ pbcAdicProjection X (pbcIntegralDatum l F) n.unop
    have hsY : pbcScalarCoefficientMap l E F i Y ≫
        pbcAdicProjection Y (pbcIntegralDatum l F) n.unop =
      pbcAdicProjection Y (pbcIntegralDatum l E) n.unop ≫
        AdicCoefficients.coefficientMap Y (pbcScalarQuotientMap l E F i n.unop) :=
      (pbcScalarCoefficientMap_exists l E F i Y).exists.choose_spec n.unop
    have hsX : pbcScalarCoefficientMap l E F i X ≫
        pbcAdicProjection X (pbcIntegralDatum l F) n.unop =
      pbcAdicProjection X (pbcIntegralDatum l E) n.unop ≫
        AdicCoefficients.coefficientMap X (pbcScalarQuotientMap l E F i n.unop) :=
      (pbcScalarCoefficientMap_exists l E F i X).exists.choose_spec n.unop
    rw [Category.assoc, hp, ← Category.assoc, ← L.map_comp,
      hsY,
      L.map_comp, Category.assoc, pbcScalarFiniteStructureSquare]
    rw [Category.assoc, hsX]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ AdicCoefficients.coefficientMap X
        (pbcScalarQuotientMap l E F i n.unop))
      (hp (pbcIntegralDatum l E) n.unop).symm
  have hd : pbcScalarCoefficientMap l E F i Y ≫
      completedCoefficientDirectImageMap g (pbcIntegralDatum l F) =
    completedCoefficientDirectImageMap g (pbcIntegralDatum l E) ≫
      D.map (pbcScalarCoefficientMap l E F i X) := by
    exact (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv_naturality_left_square
      (pbcScalarCoefficientMap l E F i Y) _ _ _ hc
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun k ↦ k.hom.app U x) hd


/-- The ambient ordinary-pullback comparison is the normalized derived tensor comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarOrdinaryPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l F) ≅
      pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  pbcActualScalarDerivedPullIso g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The direct-image comparison is the actual mate, rather than a selected isomorphism.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarDirectImageMap :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ⟶
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  pbcActualScalarDirectImageMap g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The canonical scalar/direct-image mate is invertible for finite coefficient extensions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the target valuation ring is finite free over the source. Locally choose a
finite free basis. Scalar extension is then a finite sum, and derived direct image
commutes with finite sums. The resulting identification has the same ordinary
tensor formula as the mate, so descends independently of that basis. Equivalently
use the finite perfect projection formula and the tensor-unit normalization. -/
@[instance] theorem pbcScalarDirectImageMap_isIso :
    IsIso (pbcScalarDirectImageMap l E F i g) := by
  sorry

/-- The canonical invertible direct-image comparison, with its mate definition retained.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarDirectImageIso :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ≅
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  asIso (pbcScalarDirectImageMap l E F i g)

/-- Scalar extension commutes with completion through the actual quotient augmentation.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: finite free coefficient extension commutes with products and derived inverse
limits. The uniformizer ideals in the two integer rings induce cofinal adic
filtrations. Their reductions therefore have the same completed tensor limit.
The actual finite projection maps identify their quotient augmentations. This
constructs the isomorphism with the displayed equation. Completion units are
universal for maps to complete objects, proving uniqueness. -/
theorem pbcScalarCompletionIso_exists (W : Scheme.{u}) :
    ∃! e : pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W,
      ∀ K : PbcCompletedDerived W (pbcIntegralDatum l E),
        (pbcActualCompletionUnit (pbcIntegralDatum l F) W).app
            ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫ e.hom.app K =
          (pbcEmbeddingAmbientTensor l E F i W).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) := by
  sorry

/-- The unique completion comparison preserving the specified quotient unit.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarCompletionIso (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W :=
  (pbcScalarCompletionIso_exists l E F i W).exists.choose

/-- Completed scalar/pullback is the ordinary comparison followed by the canonical
completion comparisons. Source: blueprint order 1307
(blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  isoWhiskerLeft _ (Iso.refl (pbcActualCompletedPull g (pbcIntegralDatum l F))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (pbcScalarOrdinaryPullIso l E F i g) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (pbcScalarCompletionIso l E F i X) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Iso.refl (pbcActualCompletedPull g (pbcIntegralDatum l E))).symm _

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a)

/-- First route: completed E-exchange followed by the coefficient comparisons.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarExchangeLeft :
    (pbcActualDerivedPush f (pbcIntegralDatum l E) ⋙
        pbcActualCompletedPull a (pbcIntegralDatum l E)) ⋙
      pbcEmbeddingAmbientTensor l E F i Y' ⟶
    (pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualCompletedPull g' (pbcIntegralDatum l F)) ⋙
      pbcActualDerivedPush f' (pbcIntegralDatum l F) :=
    whiskerRight (pbcActualCompletedExchange (pbcIntegralDatum l E) sq)
        (pbcEmbeddingAmbientTensor l E F i Y') ≫
      whiskerLeft (pbcActualCompletedPull g' (pbcIntegralDatum l E))
        (pbcScalarDirectImageIso l E F i f').hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (pbcScalarCompletedPullIso l E F i g').inv
        (pbcActualDerivedPush f' (pbcIntegralDatum l F))

/-- Second route: coefficient comparisons followed by completed F-exchange.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarExchangeRight :
    (pbcActualDerivedPush f (pbcIntegralDatum l E) ⋙
        pbcActualCompletedPull a (pbcIntegralDatum l E)) ⋙
      pbcEmbeddingAmbientTensor l E F i Y' ⟶
    (pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualCompletedPull g' (pbcIntegralDatum l F)) ⋙
      pbcActualDerivedPush f' (pbcIntegralDatum l F) :=
    (Functor.associator _ _ _).hom ≫
      whiskerLeft (pbcActualDerivedPush f (pbcIntegralDatum l E))
        (pbcScalarCompletedPullIso l E F i a).inv ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (pbcScalarDirectImageIso l E F i f).hom
        (pbcActualCompletedPull a (pbcIntegralDatum l F)) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (pbcEmbeddingAmbientTensor l E F i X)
        (pbcActualCompletedExchange (pbcIntegralDatum l F) sq) ≫
      (Functor.associator _ _ _).inv

/-- Scalar extension of the canonical completed E-exchange is the E'-exchange.
Every edge of this equality is an actual previously defined comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: before completion, both paths are mates of the same coefficient-change
and pullback-composition square. On flat-term K-flat representatives that square
is associativity of ordinary tensor and fiber-product pasting. Mates preserve
composition, so the ambient exchanges agree. The completion comparisons preserve
the actual quotient unit; their uniqueness gives the same compatibility after
completion and with the direct-image/completion comparison. This is the displayed
equality, and it holds before a constructibility condition is imposed. -/
theorem pbcScalarCompletedExchange :
    pbcScalarExchangeLeft l E F i sq = pbcScalarExchangeRight l E F i sq := by
  sorry

/-- The completed exchange equation persists in the actual raw rational category.
The two endpoint membership hypotheses follow whenever the displayed operations
preserve the integral constructible categories. Both sides are the localization
of the specified ambient routes, not chosen transformations between their endpoints.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the ambient exchange equation equates the two actual components. The full
inclusion is faithful, so the same equality holds for its lifted integral arrows.
Apply the actual localization functor. The unique component specifications in
rational transport identify these maps with the composites of the restricted and
rationalized comparisons and exchanges, on every rational object. Naturality on
all rational arrows follows by balancing from integral naturality. -/
theorem pbcScalarCompletedExchange_rational
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (hL : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i Y').obj
        ((pbcActualCompletedPull a (pbcIntegralDatum l E)).obj
          ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K))))
    (hR : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l F)
      ((pbcActualDerivedPush f' (pbcIntegralDatum l F)).obj
        ((pbcActualCompletedPull g' (pbcIntegralDatum l F)).obj
          ((pbcEmbeddingAmbientTensor l E F i X).obj K)))) :
    (pbcRationalization Y' (pbcIntegralDatum l F) (pbcUniformizer l F)).map
      (ObjectProperty.homMk (X := ⟨_, hL⟩) (Y := ⟨_, hR⟩)
        ((pbcScalarExchangeLeft l E F i sq).app K)) =
    (pbcRationalization Y' (pbcIntegralDatum l F) (pbcUniformizer l F)).map
      (ObjectProperty.homMk (X := ⟨_, hL⟩) (Y := ⟨_, hR⟩)
        ((pbcScalarExchangeRight l E F i sq).app K)) := by
  rw [pbcScalarCompletedExchange l E F i sq]

/-- Both ambient scalar comparisons preserve the canonical derived shift structures.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the ordinary tensor comparisons commute with shifts term by term. The
universal derived counits and units fix their descendants uniquely. The completion
comparison is fixed by the quotient augmentation, which has the same shift identity.
Thus both natural transformations satisfy the displayed CommShift equations. -/
theorem pbcScalarOperations_shift :
    NatTrans.CommShift (pbcScalarDirectImageIso l E F i g).hom ℤ ∧
      NatTrans.CommShift (pbcScalarCompletedPullIso l E F i g).hom ℤ := by
  sorry

/-- The scalar comparisons respect identity scheme morphisms with their canonical units.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the ordinary identity comparison is restriction along identity fiber-product
pasting. The coefficient square on its sections is the identity coefficient square.
Its tensor-adjunction conjugate therefore has the ordinary tensor-unit formula.
The derived counits descend that formula, and conjugacy gives the same identity
for the direct-image mate. These are precisely the two displayed equations. -/
theorem pbcScalarOperations_identity (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    ((pbcScalarDirectImageIso l E F i (𝟙 W)).hom.app K ≫
        (pbcActualDerivedDirectIdIso (pbcIntegralDatum l F) W).hom.app
          ((pbcEmbeddingAmbientTensor l E F i W).obj K) =
      (pbcEmbeddingAmbientTensor l E F i W).map
        ((pbcActualDerivedDirectIdIso (pbcIntegralDatum l E) W).hom.app K)) ∧
    ((pbcScalarOrdinaryPullIso l E F i (𝟙 W)).hom.app K ≫
        (pbcEmbeddingAmbientTensor l E F i W).map
          ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) W).hom.app K) =
      (pbcActualDerivedPullIdIso (pbcIntegralDatum l F) W).hom.app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K)) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarCompletedPullUnit_eq (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcActualCompletedPullUnit g (pbcIntegralDatum l F)).app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcScalarCompletedPullIso l E F i g).hom.app K =
    (pbcScalarOrdinaryPullIso l E F i g).hom.app K ≫
      (pbcEmbeddingAmbientTensor l E F i X).map
        ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K) := by
  unfold pbcScalarCompletedPullIso
  dsimp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Iso.symm_hom, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  change (pbcActualCompletionUnit (pbcIntegralDatum l F) X).app _ ≫
      (pbcActualCompletion (pbcIntegralDatum l F) X).map
        ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫ _ = _
  rw [← Category.assoc, ← (pbcActualCompletionUnit (pbcIntegralDatum l F) X).naturality,
    Category.assoc]
  unfold pbcScalarCompletionIso
  have hc := (pbcScalarCompletionIso_exists l E F i X).exists.choose_spec
    ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)
  simpa only [Functor.id_map, Functor.comp_obj, pbcActualCompletedPullUnit,
    whiskerLeft_app] using congrArg
      (fun f ↦ (pbcScalarOrdinaryPullIso l E F i g).hom.app K ≫ f) hc


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed identity coherence uses the canonical comparison on complete objects.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: precompose both routes with the ordinary-to-completed pullback unit. The
unit-normalized scalar completion comparison reduces both routes to the ordinary
identity coherence. Both source objects are complete, so the reflector universal
property cancels this unit and gives the displayed equality. -/
theorem pbcScalarCompletedPull_identity (W : Scheme.{u})
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    (pbcScalarCompletedPullIso l E F i (𝟙 W)).hom.app K.obj ≫
        (pbcEmbeddingAmbientTensor l E F i W).map
          ((pbcActualCompletedPullIdIso (pbcIntegralDatum l E) W).hom.app K) =
      (pbcActualCompletedPullIdIso (pbcIntegralDatum l F) W).hom.app
        ⟨(pbcEmbeddingAmbientTensor l E F i W).obj K.obj,
          pbcScalarPreservesComplete l E F i W K⟩ := by
  let K' : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)) :=
    ⟨_, pbcScalarPreservesComplete l E F i W K⟩
  let u := (pbcActualCompletedPullUnit (𝟙 W) (pbcIntegralDatum l F)).app K'.obj
  have hu : u ≫ (pbcActualCompletedPullIdIso (pbcIntegralDatum l F) W).hom.app K' =
      (pbcActualDerivedPullIdIso (pbcIntegralDatum l F) W).hom.app K'.obj :=
    (pbcActualCompletedPullIdIso_exists (pbcIntegralDatum l F) W).exists.choose_spec K'
  have : IsIso u := by
    have he : u = (pbcActualDerivedPullIdIso (pbcIntegralDatum l F) W).hom.app K'.obj ≫
        (pbcActualCompletedPullIdIso (pbcIntegralDatum l F) W).inv.app K' := by
      rw [← hu, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id u).symm
    rw [he]
    infer_instance
  apply (cancel_epi u).mp
  change u ≫ _ = u ≫ (pbcActualCompletedPullIdIso (pbcIntegralDatum l F) W).hom.app K'
  rw [← Category.assoc, pbcScalarCompletedPullUnit_eq]
  rw [Category.assoc, ← Functor.map_comp]
  unfold pbcActualCompletedPullIdIso
  rw [(pbcActualCompletedPullIdIso_exists (pbcIntegralDatum l E) W).exists.choose_spec K]
  exact (pbcScalarOperations_identity l E F i W K.obj).2.trans hu.symm

variable {Z : Scheme.{u}} (h : Z ⟶ X)

/-- Direct-image comparison respects composition with its canonical adjunction pasting.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the counit of a composite adjunction is the composite of its two counits.
Tensoring those counits with one is consequently the same projection mate on
both paths. The canonical balancing comparison identifies their coefficients,
and the derived universal comparisons preserve this equality. -/
theorem pbcScalarDirectImage_comp
    (K : PbcCompletedDerived Z (pbcIntegralDatum l E)) :
    (pbcScalarDirectImageIso l E F i g).hom.app
        ((pbcActualDerivedPush h (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPush g (pbcIntegralDatum l F)).map
        ((pbcScalarDirectImageIso l E F i h).hom.app K) ≫
      (pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l F)).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Z).obj K) =
    (pbcEmbeddingAmbientTensor l E F i Y).map
        ((pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l E)).hom.app K) ≫
      (pbcScalarDirectImageIso l E F i (h ≫ g)).hom.app K := by
  sorry

/-- The ordinary pullback comparison respects the same canonical pasting.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: on flat-term K-flat models both paths are the ordinary adjunction conjugate
of the sectionwise coefficient square for the iterated fiber product. Its pasting
is the coefficient square for the composite. Universal derived counits descend
that equality, with the indicated composition comparisons retained. -/
theorem pbcScalarOrdinaryPull_comp
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcActualDerivedPull h (pbcIntegralDatum l F)).map
        ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E F i h).hom.app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l F)).inv.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcScalarOrdinaryPullIso l E F i (h ≫ g)).hom.app K ≫
      (pbcEmbeddingAmbientTensor l E F i Z).map
        ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).hom.app K) := by
  sorry

/-- Completed pullback comparison respects composition with its actual unit pasting.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the ordinary composition equation holds on resolving tensor models.
Each completed comparison preserves the actual quotient unit. Both resulting
composites therefore extend the same ordinary map into the same complete object.
The reflection property identifies them, with the specified composition comparisons. -/
theorem pbcScalarCompletedPull_comp
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) :
    (pbcActualCompletedPull h (pbcIntegralDatum l F)).map
        ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj) ≫
      (pbcScalarCompletedPullIso l E F i h).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj) =
    (pbcActualCompletedPullCompIso h g (pbcIntegralDatum l F)).hom.app
        ⟨(pbcEmbeddingAmbientTensor l E F i Y).obj K.obj,
          pbcScalarPreservesComplete l E F i Y K⟩ ≫
      (pbcScalarCompletedPullIso l E F i (h ≫ g)).hom.app K.obj ≫
      (pbcEmbeddingAmbientTensor l E F i Z).map
        ((pbcActualCompletedPullCompIso h g (pbcIntegralDatum l E)).inv.app K) := by
  sorry

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
    (j : F →ₐ[ℚ_[l]] G)

/-- Direct-image comparison respects successive finite coefficient extensions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the two composites are projection mates with the same counit tensored
with the product coefficient. Ordinary tensor balancing sends the iterated
coefficient tensor to that product. The universal derived normalizations make
this equality independent of the chosen flat representative. -/
theorem pbcScalarDirectImage_coefficients
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l F G j Y).map
        ((pbcScalarDirectImageIso l E F i g).hom.app K) ≫
      (pbcScalarDirectImageIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) ≫
      (pbcActualDerivedPush g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j X).hom.app K) =
    (pbcAmbientScalarComp l E F G i j Y).hom.app
        ((pbcActualDerivedPush g (pbcIntegralDatum l E)).obj K) ≫
      (pbcScalarDirectImageIso l E G (j.comp i) g).hom.app K := by
  sorry

/-- Pullback comparison respects successive finite coefficient extensions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: on resolving complexes all three coefficient extensions are sheafified
tensor. The two paths multiply exactly the same coefficients in the same order.
Associativity identifies them before localization; the prescribed derived
counits give the displayed equality of derived morphisms. -/
theorem pbcScalarOrdinaryPull_coefficients
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarOrdinaryPullIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualDerivedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E G (j.comp i) g).hom.app K := by
  sorry

/-- Pullback comparison respects successive finite coefficient extensions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the ordinary comparison is balanced on K-flat models. The three coefficient
extensions are sheafified tensor. The two paths multiply exactly the same
coefficients in the same order.
Associativity identifies them before localization; the prescribed derived
counits give the displayed equality of derived morphisms. -/
theorem pbcScalarCompletedPull_coefficients
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarCompletedPullIso l E F i g).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualCompletedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) ≫
      (pbcScalarCompletedPullIso l E G (j.comp i) g).hom.app K := by
  sorry

private theorem pbcCompleteUnitCancel (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M N : PbcCompletedDerived T d)
    (hN : PbcIsIntrinsicallyComplete T d N)
    (f g : (pbcActualCompletion d T).obj M ⟶ N)
    (h : (pbcActualCompletionUnit d T).app M ≫ f =
      (pbcActualCompletionUnit d T).app M ≫ g) : f = g := by
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)
  let adj := Adjunction.ofIsRightAdjoint I
  have he : ObjectProperty.homMk
      (X := (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).leftAdjoint.obj M)
      (Y := ⟨N, hN⟩) f = ObjectProperty.homMk
        (X := (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).leftAdjoint.obj M)
        (Y := ⟨N, hN⟩) g := by
    apply (adj.homEquiv M ⟨N, hN⟩).injective
    exact h
  exact congrArg (fun k ↦ k.hom) he

/-- Completion comparison respects successive coefficients with its actual unit.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: both composites preserve the completion unit, since each comparison and
the balancing associator does. The completion reflector's uniqueness therefore
identifies them. This is also the strict quotient-tower calculation followed by
derived inverse limit, so includes every transition and the augmentation. -/
theorem pbcScalarCompletion_coefficients (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (pbcScalarCompletionIso l F G j W).hom.app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j W).map
        ((pbcScalarCompletionIso l E F i W).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j W).hom.app
        ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) =
    (pbcActualCompletion (pbcIntegralDatum l G) W).map
        ((pbcAmbientScalarComp l E F G i j W).hom.app K) ≫
      (pbcScalarCompletionIso l E G (j.comp i) W).hom.app K := by
  have hComplete : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) :=
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))).leftAdjoint.obj
      K).property
  apply pbcCompleteUnitCancel W (pbcIntegralDatum l G) _ _
    (pbcScalarPreservesComplete l E G (j.comp i) W ⟨_, hComplete⟩)
  have hEF := (pbcScalarCompletionIso_exists l E F i W).exists.choose_spec K
  have hFG := (pbcScalarCompletionIso_exists l F G j W).exists.choose_spec
    ((pbcEmbeddingAmbientTensor l E F i W).obj K)
  have hEG := (pbcScalarCompletionIso_exists l E G (j.comp i) W).exists.choose_spec K
  unfold pbcScalarCompletionIso
  -- The comparison is the unique witness whose unit equations were just obtained.
  rw [← Category.assoc, ← Category.assoc, hFG,
    ← Functor.map_comp, hEF]
  have hNat := (pbcActualCompletionUnit (pbcIntegralDatum l G) W).naturality
    ((pbcAmbientScalarComp l E F G i j W).hom.app K)
  dsimp only [Functor.id_map, Functor.comp_obj] at hNat
  erw [← Category.assoc, ← hNat, Category.assoc, hEG]
  exact (pbcAmbientScalarComp l E F G i j W).hom.naturality
    ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K)

end AmbientOperations


end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section ConditionalRestriction
variable {X Y : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A) (H : PbcCompletedDerived X d ⥤ PbcCompletedDerived Y d)
variable (h : ∀ K : PbcBoundedConstructibleComplete X d,
  PbcIsBoundedConstructibleComplete Y d (H.obj K.obj))

/-- Conditional restriction keeps exactly the actual ambient object and arrow maps.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcConditionalIntegral : PbcBoundedConstructibleComplete X d ⥤
    PbcBoundedConstructibleComplete Y d :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete Y d)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d) ⋙ H) h

/-- The actual restriction inherits addition and its constant-section linearity.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the full-subcategory inclusion changes no morphism or scalar action, so
both equations are precisely the ambient additive and linear equations. -/
theorem pbcConditionalIntegral_linear [H.Additive] [H.Linear A] :
    (pbcConditionalIntegral d H h).Additive ∧ (pbcConditionalIntegral d H h).Linear A := by
  constructor
  · dsimp only [pbcConditionalIntegral]
    infer_instance
  · refine ⟨fun {K L} f a ↦ ?_⟩
    apply ObjectProperty.hom_ext
    exact H.map_smul a f.hom

/-- Addition on the actual conditional restriction.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcConditionalIntegral_additive [H.Additive] [H.Linear A] :
    (pbcConditionalIntegral d H h).Additive := (pbcConditionalIntegral_linear d H h).1

/-- Linearity on the actual conditional restriction.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcConditionalIntegral_linearInstance [H.Additive] [H.Linear A] :
    (pbcConditionalIntegral d H h).Linear A := (pbcConditionalIntegral_linear d H h).2

/-- Rationalizing a preserving actual operation uses the tensor base-change Hom map.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcConditionalRational (p : A) [H.Additive] [H.Linear A] :
    PbcRationalCategory X d p ⥤ PbcRationalCategory Y d p :=
  ScalarLocalization.transport A p (pbcConditionalIntegral d H h)
attribute [-instance] ULift.module in
private theorem pbcConditionalRational_tmul (p : A) [H.Additive] [H.Linear A]
    (K L : PbcBoundedConstructibleComplete X d)
    (a : Localization.Away p) (f : K ⟶ L) :
    (pbcConditionalRational d H h p).map (a ⊗ₜ[A] f) =
      a ⊗ₜ[A] (pbcConditionalIntegral d H h).map f := by
  simp [pbcConditionalRational, ScalarLocalization.transport, ScalarLocalization.transportHom]

end ConditionalRestriction

section ConditionalOperations
variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Actual direct image and completed pullback retain constant coefficient scalars.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: ordinary direct image uses the unchanged additive section maps. Its module
action commutes with constant coefficients by the finite quotient formulas.
Derived localization preserves this identity. Ordinary pullback is tensor linear,
and the completion unit identifies the two scalar actions on its reflection. -/
theorem pbcActualOperations_linear :
    (pbcActualDerivedPush g (pbcIntegralDatum l E)).Additive ∧
    (pbcActualDerivedPush g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) ∧
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Additive ∧
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) := by
  sorry

/-- Additivity of actual derived direct image.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcActualPush_additive : (pbcActualDerivedPush g (pbcIntegralDatum l E)).Additive :=
  (pbcActualOperations_linear l E g).1

/-- Constant scalar linearity of actual derived direct image.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcActualPush_linear :
    (pbcActualDerivedPush g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) :=
  (pbcActualOperations_linear l E g).2.1

/-- Additivity of actual completed pullback.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcActualCompletedPull_additive :
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Additive :=
  (pbcActualOperations_linear l E g).2.2.1

/-- Constant scalar linearity of actual completed pullback.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcActualCompletedPull_linear :
    (pbcActualCompletedPull g (pbcIntegralDatum l E)).Linear (PbcIntegralRing l E) :=
  (pbcActualOperations_linear l E g).2.2.2

variable [IsNoetherian X] [IsNoetherian Y]
variable (dX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
variable (dY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
variable (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
variable (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

attribute [-instance] ULift.module in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If the actual direct images preserve constructibility, their rational comparisons
are precisely the localized ambient mate components. No preservation is assumed
without being supplied. Source: blueprint order 1307
(blueprint: prop-weil-pbc-scalar-extension).
Proof: restrict the ambient mate along the full inclusions, which changes no arrow.
Every rational object is integral. Localize each component. Naturality on pure
tensors follows from ambient naturality and semilinearity; bilinearity extends
it to all maps. All components are invertible, and their prescribed values give
uniqueness. Unit, composition, coefficient and shift equations persist under the
same functorial localization, as does the exchange equation. -/
theorem pbcScalarDirectImage_rational
    (hE : ∀ K : PbcIntegralCategory l E X dX hX,
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((pbcActualDerivedPush g (pbcIntegralDatum l E)).obj K.obj))
    (hF : ∀ K : PbcIntegralCategory l F X dX hX,
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l F)
        ((pbcActualDerivedPush g (pbcIntegralDatum l F)).obj K.obj)) :
    ∃! e :
      pbcConditionalRational (pbcIntegralDatum l E)
          (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i Y dY hY ≅
      pbcRationalScalarExtension l E F i X dX hX ⋙
        pbcConditionalRational (pbcIntegralDatum l F)
          (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF (pbcUniformizer l F),
      ∀ K : PbcRationalDerivedCategory l E X dX hX,
        HEq (e.hom.app K)
          ((pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)).map
            (ObjectProperty.homMk
              (X := (pbcEmbeddingIntegralTensor l E F i Y dY hY).obj
                ((pbcConditionalIntegral (pbcIntegralDatum l E)
                  (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE).obj K.obj))
              (Y := (pbcConditionalIntegral (pbcIntegralDatum l F)
                (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF).obj
                  ((pbcEmbeddingIntegralTensor l E F i X dX hX).obj K.obj))
              ((pbcScalarDirectImageIso l E F i g).hom.app K.obj.obj))) := by
  let eK (K : PbcRationalDerivedCategory l E X dX hX) :=
    (pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
      (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l F))
        (X := (pbcEmbeddingIntegralTensor l E F i Y dY hY).obj
          ((pbcConditionalIntegral (pbcIntegralDatum l E)
            (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE).obj K.obj))
        (Y := (pbcConditionalIntegral (pbcIntegralDatum l F)
          (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF).obj
            ((pbcEmbeddingIntegralTensor l E F i X dX hX).obj K.obj))
        ((pbcScalarDirectImageIso l E F i g).app K.obj.obj))
  have hn {K L : PbcRationalDerivedCategory l E X dX hX} (f : K ⟶ L) :
      ((pbcConditionalRational (pbcIntegralDatum l E)
        (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE (pbcUniformizer l E)) ⋙
        pbcRationalScalarExtension l E F i Y dY hY).map f ≫ (eK L).hom =
      (eK K).hom ≫ ((pbcRationalScalarExtension l E F i X dX hX) ⋙
        pbcConditionalRational (pbcIntegralDatum l F)
          (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF (pbcUniformizer l F)).map f := by
    dsimp only [Functor.comp_map]
    change pbcRationalScalarHom l E F i Y dY hY _ _
        ((pbcConditionalRational (pbcIntegralDatum l E)
          (pbcActualDerivedPush g (pbcIntegralDatum l E)) hE (pbcUniformizer l E)).map f) ≫
        (eK L).hom =
      (eK K).hom ≫ (pbcConditionalRational (pbcIntegralDatum l F)
        (pbcActualDerivedPush g (pbcIntegralDatum l F)) hF (pbcUniformizer l F)).map
          (pbcRationalScalarHom l E F i X dX hX _ _ f)
    dsimp only [pbcConditionalRational, ScalarLocalization.transport,
      ScalarLocalization.transportHom]
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_comp, comp_zero]
    | tmul a f =>
      erw [LinearMap.baseChange_tmul, pbcRationalScalarHom_tmul,
        pbcRationalScalarHom_tmul, LinearMap.baseChange_tmul]
      dsimp only [eK, Functor.mapIso_hom, pbcRationalization,
        ScalarLocalization.localization]
      change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (_ ⊗ₜ[_] _) =
        ScalarLocalization.composition _ _ _ _ _ _ (_ ⊗ₜ[_] _) (1 ⊗ₜ[_] _)
      erw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
        one_mul, mul_one]
      congr 1
      apply ObjectProperty.hom_ext
      exact (pbcScalarDirectImageIso l E F i g).hom.naturality f.hom
    | add f f' hf hf' =>
      simp only [_root_.map_add]
      erw [Preadditive.add_comp, Preadditive.comp_add]
      exact congrArg₂ (· + ·) hf hf'
  refine ⟨NatIso.ofComponents eK (fun f ↦ hn f), ?_, ?_⟩
  · intro K
    rfl
  · intro e he
    apply Iso.ext
    ext K
    exact eq_of_heq (he K)

attribute [-instance] ULift.module in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Under the two actual preservation hypotheses, the completed-pullback comparison
also descends with its specified localized components.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: restrict the unit-normalized ambient comparison to the full integral
subcategories. Its naturality descends on pure tensors and then by addition.
The localized inverse gives an inverse, and component specification proves
uniqueness. This uses no constructibility assertion for an arbitrary morphism. -/
theorem pbcScalarCompletedPull_rational
    (hE : ∀ K : PbcIntegralCategory l E Y dY hY,
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj))
    (hF : ∀ K : PbcIntegralCategory l F Y dY hY,
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F)
        ((pbcActualCompletedPull g (pbcIntegralDatum l F)).obj K.obj)) :
    ∃! e :
      pbcRationalScalarExtension l E F i Y dY hY ⋙
        pbcConditionalRational (pbcIntegralDatum l F)
          (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF (pbcUniformizer l F) ≅
      pbcConditionalRational (pbcIntegralDatum l E)
          (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i X dX hX,
      ∀ K : PbcRationalDerivedCategory l E Y dY hY,
        HEq (e.hom.app K)
          ((pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).map
            (ObjectProperty.homMk
              (X := (pbcConditionalIntegral (pbcIntegralDatum l F)
                (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF).obj
                  ((pbcEmbeddingIntegralTensor l E F i Y dY hY).obj K.obj))
              (Y := (pbcEmbeddingIntegralTensor l E F i X dX hX).obj
                ((pbcConditionalIntegral (pbcIntegralDatum l E)
                  (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE).obj K.obj))
              ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj.obj))) := by
  let eK (K : PbcRationalDerivedCategory l E Y dY hY) :=
    (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
      (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F))
        (X := (pbcConditionalIntegral (pbcIntegralDatum l F)
          (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF).obj
            ((pbcEmbeddingIntegralTensor l E F i Y dY hY).obj K.obj))
        (Y := (pbcEmbeddingIntegralTensor l E F i X dX hX).obj
          ((pbcConditionalIntegral (pbcIntegralDatum l E)
            (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE).obj K.obj))
        ((pbcScalarCompletedPullIso l E F i g).app K.obj.obj))
  have hn {K L : PbcRationalDerivedCategory l E Y dY hY} (f : K ⟶ L) :
      ((pbcRationalScalarExtension l E F i Y dY hY) ⋙
        pbcConditionalRational (pbcIntegralDatum l F)
          (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF (pbcUniformizer l F)).map f ≫
        (eK L).hom =
      (eK K).hom ≫ ((pbcConditionalRational (pbcIntegralDatum l E)
        (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE (pbcUniformizer l E)) ⋙
        pbcRationalScalarExtension l E F i X dX hX).map f := by
    dsimp only [Functor.comp_map]
    change (pbcConditionalRational (pbcIntegralDatum l F)
        (pbcActualCompletedPull g (pbcIntegralDatum l F)) hF (pbcUniformizer l F)).map
          (pbcRationalScalarHom l E F i Y dY hY _ _ f) ≫ (eK L).hom =
      (eK K).hom ≫ pbcRationalScalarHom l E F i X dX hX _ _
        ((pbcConditionalRational (pbcIntegralDatum l E)
          (pbcActualCompletedPull g (pbcIntegralDatum l E)) hE (pbcUniformizer l E)).map f)
    dsimp only [pbcConditionalRational, ScalarLocalization.transport,
      ScalarLocalization.transportHom]
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_comp, comp_zero]
    | tmul a f =>
      erw [pbcRationalScalarHom_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, pbcRationalScalarHom_tmul]
      dsimp only [eK, Functor.mapIso_hom, pbcRationalization,
        ScalarLocalization.localization]
      change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (_ ⊗ₜ[_] _) =
        ScalarLocalization.composition _ _ _ _ _ _ (_ ⊗ₜ[_] _) (1 ⊗ₜ[_] _)
      erw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
        one_mul, mul_one]
      congr 1
      apply ObjectProperty.hom_ext
      exact (pbcScalarCompletedPullIso l E F i g).hom.naturality f.hom
    | add f f' hf hf' =>
      simp only [_root_.map_add]
      erw [Preadditive.add_comp, Preadditive.comp_add]
      exact congrArg₂ (· + ·) hf hf'
  refine ⟨NatIso.ofComponents eK (fun f ↦ hn f), ?_, ?_⟩
  · intro K
    rfl
  · intro e he
    apply Iso.ext
    ext K
    exact eq_of_heq (he K)

end ConditionalOperations
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Finite coefficient extension on the actual raw rational categories has the
specified exact coherent tensor structure. The ambient, completion, conditional
restriction, and exchange clauses are stated by the companion declarations in
this module, with their actual canonical constructions above.
Source: blueprint order 1307; Milne, Lectures on Etale Cohomology, Section 19
(blueprint: prop-weil-pbc-scalar-extension).

Complete natural-language proof (all eight steps of the node):

1. Put $A=\mathcal O_E$, $B=\mathcal O_{E'}$, $t=\varpi_E$, $v=\varpi_{E'}$, $R_T=\widehat A_T$,
$S_T=\widehat B_T$. By [lem-weil-finite-free-completed-scalar-comparison], $S_T$ is a finite free
$R_T$-module and, for derived $t$-complete $K$, $K\otimes^L_{R_T}S_T$ is derived $v$-complete and
is canonically the completed integral scalar extension. The local-completeness and intrinsic
Koszul-completeness conventions agree by [lem-weil-pbc-constant-completion-equivalence]. Apply
[lem-weil-pbc-integral-stratified-perfect-characterization] to $K\in\Dbc(T,\mathcal O_E)$: on a
finite stratification it has local models $R_T\otimes_A^LP$ with $P$ bounded finite projective
over $A$. For each stratum inclusion and each pro-etale localization, the completed coefficient
sheaves restrict to the corresponding coefficient sheaves: for the scheme inclusion use
[lem-weil-pbc-profinite-coefficient-inverse-image], and for a slice localization restriction
commutes with the defining limits. Tensoring a model with $S_T$ gives $S_T\otimes_B^L(B\otimes_A
P)$. Each term of $B\otimes_A P$ is finite projective, since a splitting $P^i\oplus Q^i=A^{r_i}$
remains a splitting after tensoring. The same finite stratification and local termwise bounds
therefore give condition (ii) of that characterization over $B$. Its implication (ii) to (i)
supplies all the uniform tower and compatible etale-witness requirements of the PBC category. This
proves membership without identifying the PBC category with a different coefficient formalism.

2. The ordinary ring-sheaf change of rings $K\mapsto K\otimes^L_{R_T}S_T$ is exact by
[lem-pur-derived-change-of-rings]. By [lem-weil-pbc-uniform-complete-triangulated] the source and
target PBC integral categories have exactly the inherited triangles. Step 1 shows that the exact
ambient functor restricts to them. On integral morphisms its $A$-linearity is the identity
$(af)\otimes1=a(f\otimes1)$ on tensor representatives. Define the rational functor on morphisms by
$f/t^n\mapsto F(f)/t^n$. This is well-defined under the balancing and localization relations in
[def-weil-linear-scalar-localization]. The image of $t$ is invertible in the target rational
category: by [lem-weil-l-adic-extension-integers-dvr], the nonzero nonunit $t\in B$ is $uv^e$ for
a unit $u$ and $e\geq1$. Localization at $t$ and at $v$ gives the same morphism modules because
$v^{-1}=uv^{e-1}t^{-1}$ and $t^{-1}=u^{-1}v^{-e}$. By
[lem-weil-linear-scalar-localization-triangulated], every rational distinguished triangle is
isomorphic to a localized integral triangle; its image is consequently distinguished. This proves
exactness of the displayed functor on the raw rationalizations.

3. For three nested coefficient rings $R\to S\to U$, choose a K-flat resolution $P$ with flat
terms by [lem-pc-kflat-resolution]. Such representatives compute derived change of rings by
[lem-pur-derived-change-of-rings]; $P\otimes_R S$ is again K-flat with flat terms by
[lem-pur-kflat-change-of-rings]. Define the associator by $((p\otimes s)\otimes u)\mapsto p\otimes
su$, with inverse $p\otimes u\mapsto(p\otimes1)\otimes u$. These maps respect balancing,
restrictions and differentials. They are mutually inverse and commute with every chain map of
representatives. They hence descend through the derived localizations, and through scalar
localization by the formula of step 2. Comparison with completed scalar extension is the natural
comparison of step 1; choose these balanced maps as the specified associators for that
realization. Replace the identity-extension functor by the literal identity via multiplication
$p\otimes r\mapsto rp$. When any two adjacent fields coincide define the associator through this
unit identification.

4. For four coefficient rings $R\to S\to U\to V$, every route around the associativity pentagon
sends $(((p\otimes s)\otimes u)\otimes v)$ to $p\otimes(suv)$. Associativity of ring
multiplication makes the results equal; the universal balancing relations give equality of sheaf
maps and then of complex maps. With an identity extension, multiplication by $1$ gives the two
unit equations. Use the shift comparison which is the identity on $P^{q+1}\otimes_RS$: both
differentials are $-d_P\otimes1$. Thus the associator is the same multiplication map in both
shifted complexes, proving shift compatibility. Tensoring the cone $Q^q\oplus P^{q+1}$ gives the
cone of the tensor map, with the same differential matrix, so these comparisons are comparisons of
exact functors. Equalities of these maps persist in the two localizations of step 2.

5. For any scheme morphism $f$, [lem-weil-pbc-profinite-coefficient-inverse-image] identifies
$f^{-1}R_Y=R_X$ and $f^{-1}S_Y=S_X$, naturally in the finite coefficient quotients and their ring
maps. Define the direct-image comparison by the projection mate with coefficient object $S_Y$. By
[lemma-weil-pbc-perfect-projection-formula] it is an isomorphism after restricting to
$R_Y$-modules, because $S_Y$ is finite free by step 1. This is the required $S_Y$-module arrow,
not just an arbitrary restricted isomorphism: its adjunct is the counit on $K$ tensored with
$1_{S_X}$, so multiplication by any section of $S_Y$ commutes with it. To identify the target
direct image after restricting scalars, use the module adjunction
[lem-weil-pbc-ringed-topoi-module-adjunction] for the identity topos with ring map $R_X\to S_X$.
If $J$ is K-injective over $S_X$, maps from an acyclic $R_X$-complex $C$ to its restriction
identify with maps from $C\otimes_{R_X}S_X$ to $J$. The latter complex is acyclic since $S_X$ is
finite free. Such maps are null-homotopic by [def-pur-kinjective-complex]. Thus restriction
preserves K-injectives in this case, and the underived equality
$f_*\operatorname{Res}J=\operatorname{Res}f_*J$ computes the derived equality. Restriction detects
quasi-isomorphisms, as the underlying abelian sheaves are unchanged. The projection mate is
consequently an isomorphism in the $S_Y$-derived category itself. If $K$ is derived complete,
[prop-weil-pbc-direct-image-limits] makes $Rf_*K$ derived complete, for either coefficient ring.
Together with step 1 this puts both endpoints in the claimed ambient derived-complete categories.

6. Ordinary pullback commutes with coefficient extension by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the coefficient inverse-image
identifications of step 5. Now complete this comparison. The completed pullback of
[def-weil-pbc-completed-pullback] is ordinary pullback followed by its canonical completion unit.
Finite-free tensor commutes with the Koszul completion construction: a basis of $S_{T'}$ over
$R_{T'}$ identifies it with a finite sum, finite sums commute with products, and the matrix $1-s$
in the strict-tower Roos triangle commutes with that finite sum. The canonical map, defined before
choosing the basis, is therefore an isomorphism and respects the completion units. The Roos
realization is [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. Completion with respect to $t$
and $v$ in $S_{T'}$ is the same reflector: $t=uv^e$ implies $S[1/t]=S[1/v]$ with the same
localization map from $S$. The extended Cech complexes for these single generators are
consequently the identical augmented complex $[S\to S[1/v]]$. By
[lem-weil-pbc-extended-cech-completion-model], derived Hom from this augmented complex realizes
both completion reflectors and their units. By [lem-weil-pbc-ringed-koszul-completion-reflector],
the Koszul completion constructions are also these reflectors, so their canonical isomorphism is
uniquely fixed by the units. This gives the claimed completed-pullback comparison without claiming
that ordinary pullback of an arbitrary complete object is complete.

7. The comparisons just constructed are coherent. For coefficient towers, take successively
tensor-product bases of the finite-free extensions. The projection comparison of step 5, after
restriction of scalars, is the direct sum of identity maps $Rf_*K\to Rf_*K$ indexed by a basis.
This follows from its counit-tensor definition and the tensor-unit case of
[lem-weil-pbc-ringed-projection-mate-exact]. Iterating two comparisons or using their associator
in step 3 gives the same identities indexed by pairs of basis elements. Changing a basis
conjugates both routes by the same scalar matrix, so the resulting equality is independent of the
bases. For composed scheme morphisms the counit of the composite adjunction is the composite of
the two counits; tensoring these with $1$ gives the same direct sums of identities. For pullback
these equations are the balanced formula of step 3 on the canonical compositions of inverse
images. For completed pullback they persist because the completion isomorphisms in step 6 are
uniquely fixed by the completion units. The same equations with a single basis element $1$ give
identity coherence. Shift coherence follows from the counit-tensor shift equation in
[lem-weil-pbc-ringed-projection-mate-exact] and the explicit shift formula in step 4.

8. Set $Q=S_Y$ in [lem-weil-pbc-ringed-exchange-tensor-coherence]. Its two equal composites say
exactly that tensoring the ambient $R$-exchange and then using the direct-image and pullback
comparisons gives the ambient exchange after coefficient extension. The $S$-actions are those of
step 5: the exchange is the mate of the same inverse-image commutation square, with counits
transported by scalar extension, so the equality is an equality of $S$-module arrows. For the
completed exchange, apply the completion functor to this equality and use step 6. The canonical
identification of completed $Rf'_*Lg'^*K$ with $Rf'_*Lg'^*_{\mathrm{comp}}K$ is computed by
$R\lim$ of the projection-formula maps for finite reductions, followed by the
direct-image/derived-limit isomorphism of [prop-weil-pbc-direct-image-limits]. For coefficient
change, compute completion on both sides with the image of $t$. Use the Koszul towers
$[R\xrightarrow{t^n}R]$ and $[S\xrightarrow{t^n}S]$: tensoring the first with $S$ gives the
second, including transition maps (multiplication by $t$ in degree $-1$, identity in degree zero)
and units. These are bounded finite-free coefficient complexes, so the projection arrows and their
exchange square apply to them. Their derived limits compute completion by step 6. The
$t$-completion of $S$ is identified with its $v$-completion by the unit-compatible reflector
comparison of that step; no equality of $t^n$- and $v^n$-reductions is used. By
[lemma-weil-pbc-projection-formula-base-change-naturality], the ambient equality commutes with
each of these specified projection maps. To obtain an equality of tower arrows, apply the same
ringed projection/exchange coherence on the diagram sites of
[lem-weil-pbc-diagram-site-realization], with $J=\mathbf N_{\geq1}^{\mathrm{op}}$. On each product
site use the completed ring sheaf constant in the $J$ direction, exactly as in that realization
statement; the quotient coefficient towers are module objects over this ring sheaf through its
quotient maps. Thus no assertion about a varying ring sheaf is required. These sites are small;
their module categories are exactly the strict diagram categories, by its additive exact
equivalence. Thus the projection mate and exchange mate calculation holds for the actual diagram
arrows, not merely at their evaluations. The derived strict-tower limit is an actual functor by
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], so applying it preserves this equality; no
faithfulness of levelwise derived evaluations is used. This is compatibility with the completion
of the specified ambient mate, including its prescribed direct-image/completion comparison, rather
than compatibility with some isomorphism between its endpoints. Finally all arrows restrict when
the operations preserve the integral constructible categories, and rationalization extends those
specified transformations by [prop-weil-pbc-rational-transport]. The denominator formula of step 2
shows that the integral equality remains the same equality for every rational morphism. This
proves the last assertion.
-/
theorem pbcCoherentScalarExtension
    {E F G H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H) :
    (pbcStageTransition l Ω T h).Additive ∧
    (pbcStageTransition l Ω T h).IsTriangulated ∧
    (pbcStageTransition l Ω T (le_refl E) = 𝟭 _) ∧
    HEq (pbcStageAssociator l Ω T (le_refl E) h)
      (Functor.leftUnitor (pbcStageTransition l Ω T h)) ∧
    HEq (pbcStageAssociator l Ω T h (le_refl F))
      (Functor.rightUnitor (pbcStageTransition l Ω T h)) ∧
    (∀ K : pbcCoefficientStage l Ω T E,
      (pbcStageTransition l Ω T h'').map ((pbcStageAssociator l Ω T h h').hom.app K) ≫
          (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
        (pbcStageAssociator l Ω T h' h'').hom.app ((pbcStageTransition l Ω T h).obj K) ≫
          (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K) ∧
    NatTrans.CommShift (pbcStageAssociator l Ω T h h').hom ℤ := by
  refine ⟨(pbcStageExact l Ω T h).1, (pbcStageExact l Ω T h).2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pbcStageAssociator_laws l Ω T).2.1 E
  · exact ((pbcStageAssociator_laws l Ω T).2.2 h).1
  · exact ((pbcStageAssociator_laws l Ω T).2.2 h).2
  · exact (pbcStageAssociator_laws l Ω T).1 h h' h''
  · exact pbcStageAssociatorShift l Ω T h h'

end AlgebraicGeometry.Scheme
