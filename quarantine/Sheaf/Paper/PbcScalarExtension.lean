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

import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Paper.CompletedTowerDirectImage
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.RingedPushforwardCompletion
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The finite coefficient map induced by the specified field embedding.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
def pbcScalarQuotientMap (n : ℕ) :
    PbcQuotient (pbcIntegralDatum l E) n →+* PbcQuotient (pbcIntegralDatum l F) n :=
  Ideal.Quotient.lift ((pbcIntegralDatum l E).ideal ^ (n + 1))
    ((Ideal.Quotient.mk ((pbcIntegralDatum l F).ideal ^ (n + 1))).comp
      (pbcEmbeddingIntegerMap l E F i))
    (pbcEmbeddingIntegerMap_quotient_kernel l E F i n)

variable (T : Scheme.{u})

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
  sorry

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
  sorry

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

/-- Completed coefficient maps compose as the actual field embeddings do.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: compose with every target finite projection. Both maps send the residue of
an integer x to the residue of j(i(x)). Quotient induction, sheafification and
joint monicity of limit projections give equality. -/
theorem pbcScalarCoefficientMap_comp :
    pbcScalarCoefficientMap l E F i T ≫ pbcScalarCoefficientMap l F G j T =
      pbcScalarCoefficientMap l E G (j.comp i) T := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The ordinary identity-on-sections restriction comparison.
Source: Stacks 03DA (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarRestrictId := (pbcScalarRestrictId_exists l E T).exists.choose

/-- The identity completed coefficient map fixes all finite projections.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the identity field embedding induces the identity on each quotient, hence
on each quotient coefficient sheaf. Limit projections are jointly monic. -/
theorem pbcScalarCoefficientMap_id :
    pbcScalarCoefficientMap l E E (AlgHom.id (Padic l) E) T =
      𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E)) := by
  sorry

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

/-- The specified unit components are natural on every localized Hom module.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: on a pure tensor this is naturality of the ambient unit and the rational
Hom formula. Additivity extends it to sums of pure tensors. -/
theorem pbcRationalScalarUnit_naturality
    (K L : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) :
    (pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv).map f ≫
        (pbcRationalScalarUnitComponent l E T hDim hInv L).hom =
      (pbcRationalScalarUnitComponent l E T hDim hInv K).hom ≫ f := by
  sorry

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
  sorry

/-- The tensor shift comparison normalized by its actual derived counit.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcAmbientScalarShift : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ :=
  (pbcAmbientScalarShift_exists l E F i T).exists.choose

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
  sorry

/-- The inherited integral shift, fixed by the ambient inclusion equation.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
instance pbcIntegralScalarShift :
    (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ :=
  (pbcIntegralScalarShift_exists l E F i T).exists.choose

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
  sorry

/-- The integral-to-rational tensor square has identity components on objects.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarLocalizationIso :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F) ≅
      pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i T dim.out inv.out :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ pbcScalarLocalization_naturality l E F i T f)

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
  sorry

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
  sorry

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
  sorry

/-- Actual inclusions compose as direct inclusions.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: both maps send each subfield element to its same ambient scalar. -/
theorem pbcSubfieldInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    (pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h) =
      pbcSubfieldInclusion l Ω (h.trans h') := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry
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
  sorry

end AlgebraicGeometry.Scheme
