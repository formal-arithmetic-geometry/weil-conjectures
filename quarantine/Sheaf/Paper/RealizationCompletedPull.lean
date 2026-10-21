/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.PbcActualRingedExchange
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.PbcRationalTransport
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-! # Completion-unit-normalized realization and pullback

Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-completed-pull)

The records retain actual strict-tower completion units. Ordinary scalar comparisons
are fixed on tensor units and on resolving complexes, rather than chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures

/-- The schemes quantified over in BS Remark 6.8.15, with the explicit finiteness
and invertibility conventions of this node. No nonemptiness condition is imposed.
Source: BS 6.6.11, 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
structure RealizationPullScheme (l : ℕ) (k : Type u) [Field k] where
  scheme : Scheme.{u}
  [over : scheme.Over (Spec (.of k))]
  [finiteType : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [quasiCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]
  [noetherian : IsNoetherian scheme]
  [dimension : Fact (∃ n : ℕ, topologicalKrullDim scheme ≤ n)]
  [invertible : Fact (∀ t : scheme, IsUnit (l : scheme.presheaf.stalk t))]

attribute [instance] RealizationPullScheme.over RealizationPullScheme.finiteType
  RealizationPullScheme.quasiCompact RealizationPullScheme.separated
  RealizationPullScheme.noetherian RealizationPullScheme.dimension RealizationPullScheme.invertible

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k]

/-- Sectionwise coordinates for the archived scalar realization.
Source: BS 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
@[irreducible] def realizationPullScalarMap {T : Scheme.{u}}
    [IsNoetherian T] [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) := s.integralIso.hom ≫ s.inclusion

/-- The local fraction 1/varpi^n in the continuous rational coefficient sheaf.
Source: BS 6.8.2 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullDenominator (T : Scheme.{u}) (W : T.ProEtᵒᵖ) (n : ℕ) :
    (rationalCoefficientSheaf l T E).obj.obj W := by
  let e : E := ((Padic.coefficientExtensionUniformizer l E :
    Padic.coefficientExtensionIntegers l E) : E) ^ n
  letI := coefficientExtensionNormedField l E
  exact ContinuousMap.const W.unop.left (ULift.up e⁻¹)

/-- The scalar realization on raw rationalizations in the same sectionwise coordinates.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullRationalScalar {T : Scheme.{u}}
    [IsNoetherian T] [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) :=
  letI := s.encodingAdditive
  letI := s.encodingInverseAdditive
  s.J ⋙ (boundedConstructible
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).ι ⋙
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T
        ((adicLisseForget T).mapIso s.sectionIso).symm)).mapDerivedCategory.functor

/-- The published scalar functor's integral comparison with the named scalar map.
Only definitional presentation is changed; this is exactly s.integral.
Source: BS 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullIntegral {T : Scheme.{u}}
    [IsNoetherian T] [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) :
    pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        realizationPullRationalScalar l E s ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (realizationPullScalarMap l E s) := by
  letI := s.encodingAdditive
  letI := s.encodingInverseAdditive
  delta realizationPullRationalScalar realizationPullScalarMap
  exact s.integral

variable {l E k}

/-- The scalar comparison for one morphism, retaining its tensor-unit and derived
representative normalizations and the specified strict quotient-tower unit.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
structure RealizationCompletedPullCoefficients
    (T U : RealizationPullScheme l k) (h : T.scheme ⟶ U.scheme)
    (sT : RealizationScalarFunctorData l E T.scheme)
    (sU : RealizationScalarFunctorData l E U.scheme) where
  coefficient_isIso : IsIso (completedCoefficientMap h (pbcIntegralDatum l E))
  coefficient_normalization : integralCoefficientRestrictionNormalized l E h
      ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map sU.integralIso.inv ≫
        completedCoefficientMap h (pbcIntegralDatum l E) ≫ sT.integralIso.hom)
  rationalCoefficient : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l U.scheme E) ≅ rationalCoefficientSheaf l T.scheme E
  rational_normalization : rationalCoefficientRestrictionNormalized l E h rationalCoefficient.hom
  coefficient_square : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (realizationPullScalarMap l E sU) ≫ rationalCoefficient.hom =
      completedCoefficientMap h (pbcIntegralDatum l E) ≫ realizationPullScalarMap l E sT

/-- The actual ordinary and completed integral pullbacks with the specified unit.
Source: BS 6.6.11 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
structure RealizationCompletedPullIntegral
    (T U : RealizationPullScheme l k) (h : T.scheme ⟶ U.scheme) where
  ordinary_mem : ∀ K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)
      ((pbcActualDerivedPull h (pbcIntegralDatum l E)).obj K.obj)
  completed_mem : ∀ K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) h).obj K.obj)
  unit_isIso : ∀ K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
    IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app K.obj)
  ordinaryAdditive : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPull h (pbcIntegralDatum l E)) ordinary_mem).Additive
  ordinaryLinear : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPull h (pbcIntegralDatum l E)) ordinary_mem).Linear (PbcIntegralRing l E)
  completedAdditive : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h) completed_mem).Additive
  completedLinear : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h) completed_mem).Linear
      (PbcIntegralRing l E)

/-- The normalized scalar comparison using the actual coefficient and integral data.
Source: BS 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
structure RealizationCompletedPullArrow
    (T U : RealizationPullScheme l k) (h : T.scheme ⟶ U.scheme)
    (sT : RealizationScalarFunctorData l E T.scheme)
    (sU : RealizationScalarFunctorData l E U.scheme)
    extends RealizationCompletedPullCoefficients T U h sT sU,
      RealizationCompletedPullIntegral (E := E) T U h where
  moduleComparison : pbcActualModulePull h (pbcIntegralDatum l E) ⋙
        pbcExtend (realizationPullScalarMap l E sT) ≅
      pbcExtend (realizationPullScalarMap l E sU) ⋙
        proEtaleRingModulePullback h (rationalCoefficientSheaf l U.scheme E)
          (rationalCoefficientSheaf l T.scheme E) rationalCoefficient
  module_unit : ∀ (M : pbcModules U.scheme (pbcAdicCompletion U.scheme (pbcIntegralDatum l E)))
      (V : U.scheme.ProEt) (m : M.val.obj (op V)),
    (moduleComparison.hom.app M).val.app (op ((proEtaleBaseChange h).obj V))
        (pbcTensorSection (realizationPullScalarMap l E sT)
          ((pbcActualModulePull h (pbcIntegralDatum l E)).obj M)
          (op ((proEtaleBaseChange h).obj V)) 1
          (pbcActualModuleUnitSection h (pbcIntegralDatum l E) M V m)) =
      proEtaleRingModuleUnitSection h (rationalCoefficientSheaf l U.scheme E)
        (rationalCoefficientSheaf l T.scheme E) rationalCoefficient
        ((pbcExtend (realizationPullScalarMap l E sU)).obj M) V
        (pbcTensorSection (realizationPullScalarMap l E sU) M (op V) 1 m)
  ordinaryComparison : pbcActualDerivedPull h (pbcIntegralDatum l E) ⋙
        pbcDerivedExtend (realizationPullScalarMap l E sT) ≅
      pbcDerivedExtend (realizationPullScalarMap l E sU) ⋙
        proEtaleRingDerivedPullback h (rationalCoefficientSheaf l U.scheme E)
          (rationalCoefficientSheaf l T.scheme E) rationalCoefficient
  module_fraction : ∀ (M : pbcModules U.scheme
      (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))) (V : U.scheme.ProEt)
      (m : M.val.obj (op V)) (n : ℕ),
    (moduleComparison.hom.app M).val.app (op ((proEtaleBaseChange h).obj V))
        (pbcTensorSection (realizationPullScalarMap l E sT)
          ((pbcActualModulePull h (pbcIntegralDatum l E)).obj M)
          (op ((proEtaleBaseChange h).obj V))
          (realizationPullDenominator l E T.scheme (op ((proEtaleBaseChange h).obj V)) n)
          (pbcActualModuleUnitSection h (pbcIntegralDatum l E) M V m)) =
      proEtaleRingModuleUnitSection h (rationalCoefficientSheaf l U.scheme E)
        (rationalCoefficientSheaf l T.scheme E) rationalCoefficient
        ((pbcExtend (realizationPullScalarMap l E sU)).obj M) V
        (pbcTensorSection (realizationPullScalarMap l E sU) M (op V)
          (realizationPullDenominator l E U.scheme (op V) n) m)
  complexComparison : (pbcActualModulePull h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend (realizationPullScalarMap l E sT)).mapHomologicalComplex (.up ℤ) ≅
      (pbcExtend (realizationPullScalarMap l E sU)).mapHomologicalComplex (.up ℤ) ⋙
        (proEtaleRingModulePullback h (rationalCoefficientSheaf l U.scheme E)
          (rationalCoefficientSheaf l T.scheme E) rationalCoefficient).mapHomologicalComplex
            (.up ℤ)
  complex_terms : ∀ (P : CochainComplex
      (pbcModules U.scheme (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))) ℤ) (n : ℤ),
    (complexComparison.hom.app P).f n = moduleComparison.hom.app (P.X n)
  derived_normalization : ∀ P : CochainComplex
      (pbcModules U.scheme (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))) ℤ,
    ordinaryComparison.hom.app (DerivedCategory.Q.obj P) ≫
        (proEtaleRingDerivedPullback h (rationalCoefficientSheaf l U.scheme E)
          (rationalCoefficientSheaf l T.scheme E) rationalCoefficient).map
            (pbcComplexCounit (realizationPullScalarMap l E sU) P) ≫
        (proEtaleRingDerivedPullbackFactors h (rationalCoefficientSheaf l U.scheme E)
          (rationalCoefficientSheaf l T.scheme E) rationalCoefficient).hom.app
            (((pbcExtend (realizationPullScalarMap l E sU)).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedExtend (realizationPullScalarMap l E sT)).map
        (pbcActualPullComplexCounit h (pbcIntegralDatum l E) P) ≫
      pbcComplexCounit (realizationPullScalarMap l E sT)
        (((pbcActualModulePull h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (complexComparison.hom.app P)
  alpha : (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
        pbcActualStrictCompletedPull (pbcIntegralDatum l E) h) ⋙
        pbcDerivedExtend (realizationPullScalarMap l E sT) ≅
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (realizationPullScalarMap l E sU)) ⋙
        proEtaleRingDerivedPullback h (rationalCoefficientSheaf l U.scheme E)
          (rationalCoefficientSheaf l T.scheme E) rationalCoefficient
  alpha_normalization : ∀ K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
    (pbcDerivedExtend (realizationPullScalarMap l E sT)).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app K.obj) ≫
      alpha.hom.app K = ordinaryComparison.hom.app K.obj

/-- The actual ordinary pullback restricted to the full integral subcategory.
Source: BS 6.6.11 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def RealizationCompletedPullArrow.integralOrdinary
    {T U : RealizationPullScheme l k} {h : T.scheme ⟶ U.scheme}
    {sT : RealizationScalarFunctorData l E T.scheme}
    {sU : RealizationScalarFunctorData l E U.scheme}
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPull h (pbcIntegralDatum l E)) a.ordinary_mem

/-- The specified strict-tower completed pullback restricted to the integral category.
Source: Stacks 099N, BS 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def RealizationCompletedPullArrow.integralCompleted
    {T U : RealizationPullScheme l k} {h : T.scheme ⟶ U.scheme}
    {sT : RealizationScalarFunctorData l E T.scheme}
    {sU : RealizationScalarFunctorData l E U.scheme}
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h) a.completed_mem

/-- Ordinary pullback on raw rationalizations, with the tensor Hom map.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def RealizationCompletedPullArrow.rationalOrdinary
    {T U : RealizationPullScheme l k} {h : T.scheme ⟶ U.scheme}
    {sT : RealizationScalarFunctorData l E T.scheme}
    {sU : RealizationScalarFunctorData l E U.scheme}
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  letI := a.ordinaryAdditive
  letI := a.ordinaryLinear
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E)
    (pbcConditionalIntegral (pbcIntegralDatum l E)
      (pbcActualDerivedPull h (pbcIntegralDatum l E)) a.ordinary_mem)

/-- Completed pullback on raw rationalizations, with the same denominators.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def RealizationCompletedPullArrow.rationalCompleted
    {T U : RealizationPullScheme l k} {h : T.scheme ⟶ U.scheme}
    {sT : RealizationScalarFunctorData l E T.scheme}
    {sU : RealizationScalarFunctorData l E U.scheme}
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  letI := a.completedAdditive
  letI := a.completedLinear
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E)
    (pbcConditionalIntegral (pbcIntegralDatum l E)
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h) a.completed_mem)

/-- Continuous rational pullback with the coefficient identification obtained by localization.
Source: BS 6.8.2, 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def RealizationCompletedPullArrow.continuousPull
    {T U : RealizationPullScheme l k} {h : T.scheme ⟶ U.scheme}
    {sT : RealizationScalarFunctorData l E T.scheme}
    {sU : RealizationScalarFunctorData l E U.scheme}
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  proEtaleRingDerivedPullback h (rationalCoefficientSheaf l U.scheme E)
    (rationalCoefficientSheaf l T.scheme E) a.rationalCoefficient

/-- Morphisms over the stated base field, with no properness or square condition.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-completed-pull). -/
abbrev RealizationPullHom (T U : RealizationPullScheme l k) :=
  Over.mk (T.scheme ↘ Spec (.of k)) ⟶ Over.mk (U.scheme ↘ Spec (.of k))

set_option backward.isDefEq.respectTransparency false in
/-- Identity base change on the actual small pro-etale site, with first projection.
Source: Stacks Tag 03D8 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullSiteId (T : Scheme.{u}) :
    proEtaleBaseChange (𝟙 T) ≅ 𝟭 T.ProEt :=
  MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T

/-- A morphism with its numerator and the specified uniformizer denominator.
This uses the actual scalar action in the raw localization, without a Karoubi envelope.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullRawFraction (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) {K L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)}
    (f : K ⟶ L) (n : ℕ) :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K ⟶
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj L :=
  ((IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
    (pbcUniformizer l E)) ^ n) •
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f

section RealizationPullLaws

variable (scalar : ∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme)

variable (arrow : ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  RealizationCompletedPullArrow T U h.left (scalar T) (scalar U))

variable (rationalAlpha : ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  (arrow h).rationalCompleted ⋙ realizationPullRationalScalar l E (scalar T) ≅
    realizationPullRationalScalar l E (scalar U) ⋙ (arrow h).continuousPull)

/-- The rationalAlpha integral clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRationalAlphaIntegral : Prop :=
  ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U)
    (K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)),
  (rationalAlpha h).hom.app ⟨K⟩ ≫
      (arrow h).continuousPull.map ((realizationPullIntegral l E (scalar U)).hom.app K) =
    (realizationPullIntegral l E (scalar T)).hom.app ((arrow h).integralCompleted.obj K) ≫
      (arrow h).alpha.hom.app K

/-- The coefficient comp clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawCoefficientComp : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  (arrow (h ≫ j)).rationalCoefficient =
    proEtaleRingCompositeCoefficients h.left j.left
      (rationalCoefficientSheaf l V.scheme E) (rationalCoefficientSheaf l U.scheme E)
      (rationalCoefficientSheaf l T.scheme E)
      (arrow j).rationalCoefficient (arrow h).rationalCoefficient

variable (rationalComp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  (arrow j).continuousPull ⋙ (arrow h).continuousPull ≅ (arrow (h ≫ j)).continuousPull)

/-- The rationalComp canonical clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRationalCompCanonical : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  HEq (rationalComp h j).symm
    (integralTowerGeneralPullbackComposition h.left j.left
      (rationalCoefficientSheaf l V.scheme E) (rationalCoefficientSheaf l U.scheme E)
      (rationalCoefficientSheaf l T.scheme E)
      (arrow j).rationalCoefficient (arrow h).rationalCoefficient)

variable (completedComp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left) ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left) ≅
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ j).left)

/-- The completedComp normalization clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawCompletedCompNormalization : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V)
    (K : PbcBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)),
  (pbcActualDerivedPull h.left (pbcIntegralDatum l E)).map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) j.left).app K.obj) ≫
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).app
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left).obj K.obj) ≫
    (completedComp h j).hom.app K =
  (pbcActualDerivedPullCompIso h.left j.left (pbcIntegralDatum l E)).inv.app K.obj ≫
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ j).left).app K.obj

/-- The completedComp unique clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawCompletedCompUnique : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V)
    (K : PbcBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E))
    (q : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left).obj
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left).obj K.obj) ≅
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ j).left).obj K.obj),
  (pbcActualDerivedPull h.left (pbcIntegralDatum l E)).map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) j.left).app K.obj) ≫
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).app
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left).obj K.obj) ≫ q.hom =
    (pbcActualDerivedPullCompIso h.left j.left (pbcIntegralDatum l E)).inv.app K.obj ≫
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ j).left).app K.obj →
  q = (completedComp h j).app K

/-- The alpha comp clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawAlphaComp : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V)
    (K : PbcBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)),
  (pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).map
      ((completedComp h j).hom.app K) ≫ (arrow (h ≫ j)).alpha.hom.app K =
    (arrow h).alpha.hom.app ((arrow j).integralCompleted.obj K) ≫
      (arrow h).continuousPull.map ((arrow j).alpha.hom.app K) ≫
      (rationalComp h j).hom.app
        ((pbcDerivedExtend (realizationPullScalarMap l E (scalar V))).obj K.obj)

variable (moduleId : ∀ T : RealizationPullScheme l k,
  proEtaleRingModulePullback (𝟙 T.scheme) (rationalCoefficientSheaf l T.scheme E)
      (rationalCoefficientSheaf l T.scheme E) (arrow (𝟙 (Over.mk
        (T.scheme ↘ Spec (.of k))))).rationalCoefficient ≅ 𝟭 _)

/-- The moduleId unit clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawModuleIdUnit : Prop :=
  ∀ (T : RealizationPullScheme l k)
    (M : proEtaleRingModules T.scheme (rationalCoefficientSheaf l T.scheme E))
    (W : T.scheme.ProEt) (m : M.val.obj (op W)),
  ((moduleId T).hom.app M).val.app
      (op ((proEtaleBaseChange (𝟙 T.scheme)).obj W))
      (proEtaleRingModuleUnitSection (𝟙 T.scheme) (rationalCoefficientSheaf l T.scheme E)
        (rationalCoefficientSheaf l T.scheme E) (arrow (𝟙 (Over.mk
          (T.scheme ↘ Spec (.of k))))).rationalCoefficient M W m) =
    M.val.map ((realizationPullSiteId T.scheme).hom.app W).op m

variable (continuousId : ∀ T : RealizationPullScheme l k,
  (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).continuousPull ≅ 𝟭 _)

/-- The continuousId normalization clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawContinuousIdNormalization : Prop :=
  ∀ (T : RealizationPullScheme l k)
    (P : CochainComplex
      (proEtaleRingModules T.scheme (rationalCoefficientSheaf l T.scheme E)) ℤ),
  (continuousId T).hom.app (DerivedCategory.Q.obj P) =
    (proEtaleRingDerivedPullbackFactors (𝟙 T.scheme) (rationalCoefficientSheaf l T.scheme E)
      (rationalCoefficientSheaf l T.scheme E) (arrow (𝟙 (Over.mk
        (T.scheme ↘ Spec (.of k))))).rationalCoefficient).hom.app P ≫
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (moduleId T) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)

/-- The alpha id clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawAlphaId : Prop :=
  ∀ (T : RealizationPullScheme l k)
    (K : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)),
  (pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 T.scheme)).app K.obj) ≫
    (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).alpha.hom.app K ≫
    (continuousId T).hom.app
      ((pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).obj K.obj) =
  (pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).map
    ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T.scheme).hom.app K.obj)

/-- The rawFractions clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRawFractions : Prop :=
  ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U)
    (K L : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))
    (f : K ⟶ L) (n : ℕ),
  (arrow h).rationalOrdinary.map (X := ⟨K⟩) (Y := ⟨L⟩)
      (realizationPullRawFraction l E U.scheme f n) =
    realizationPullRawFraction l E T.scheme ((arrow h).integralOrdinary.map f) n ∧
  (arrow h).rationalCompleted.map (X := ⟨K⟩) (Y := ⟨L⟩)
      (realizationPullRawFraction l E U.scheme f n) =
    realizationPullRawFraction l E T.scheme ((arrow h).integralCompleted.map f) n

variable (rawUnit : ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  (arrow h).rationalOrdinary ≅ (arrow h).rationalCompleted)

/-- The rawUnit integral clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRawUnitIntegral : Prop :=
  ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U)
    (K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)),
  (rawUnit h).hom.app ⟨K⟩ =
    (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
      (ObjectProperty.homMk (X := (arrow h).integralOrdinary.obj K)
        (Y := (arrow h).integralCompleted.obj K)
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).app K.obj))

variable (rawComp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  (arrow j).rationalCompleted ⋙ (arrow h).rationalCompleted ≅
    (arrow (h ≫ j)).rationalCompleted)

/-- The rawComp integral clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRawCompIntegral : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V)
    (K : PbcBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)),
  (rawComp h j).hom.app ⟨K⟩ =
    (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
      (ObjectProperty.homMk
        (X := (arrow h).integralCompleted.obj ((arrow j).integralCompleted.obj K))
        (Y := (arrow (h ≫ j)).integralCompleted.obj K) ((completedComp h j).hom.app K))

variable (rawId : ∀ T : RealizationPullScheme l k,
  (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).rationalCompleted ≅ 𝟭 _)

/-- The rawId integral clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRawIdIntegral : Prop :=
  ∀ (T : RealizationPullScheme l k)
    (K : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)),
  (rawId T).hom.app ⟨K⟩ =
    (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
      (ObjectProperty.homMk
        (X := (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).integralCompleted.obj K)
        (Y := K) (@inv _ _ _ _
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 T.scheme)).app K.obj)
          ((arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).unit_isIso K) ≫
          (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T.scheme).hom.app K.obj))

/-- The rawAlpha comp clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRawAlphaComp : Prop :=
  ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V)
    (K : PbcRationalCategory V.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)),
  (realizationPullRationalScalar l E (scalar T)).map ((rawComp h j).hom.app K) ≫
      (rationalAlpha (h ≫ j)).hom.app K =
    (rationalAlpha h).hom.app ((arrow j).rationalCompleted.obj K) ≫
      (arrow h).continuousPull.map ((rationalAlpha j).hom.app K) ≫
      (rationalComp h j).hom.app ((realizationPullRationalScalar l E (scalar V)).obj K)

/-- The rawAlpha id clause of the normalized comparison system.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def realizationPullLawRawAlphaId : Prop :=
  ∀ (T : RealizationPullScheme l k)
    (K : PbcRationalCategory T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)),
  (rationalAlpha (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).hom.app K ≫
      (continuousId T).hom.app ((realizationPullRationalScalar l E (scalar T)).obj K) =
    (realizationPullRationalScalar l E (scalar T)).map ((rawId T).hom.app K)

end RealizationPullLaws

/-- Existence of the coherent scalar comparison system, fixed by its units.
The rational fields extend the same integral arrows on the raw localization.
Source: BS 6.6.11, 6.8.2 and 6.8.15
(blueprint: lem-weil-pbc-realization-completed-pull). -/
def RealizationCompletedPullData (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] : Prop :=
   ∃ scalar : (∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme),
  ∃ arrow : (∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  RealizationCompletedPullArrow T U h.left (scalar T) (scalar U)),
  ∃ rationalAlpha : (∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  (arrow h).rationalCompleted ⋙ realizationPullRationalScalar l E (scalar T) ≅
    realizationPullRationalScalar l E (scalar U) ⋙ (arrow h).continuousPull),
  realizationPullLawRationalAlphaIntegral scalar arrow rationalAlpha ∧
  realizationPullLawCoefficientComp scalar arrow ∧
  ∃ rationalComp : (∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  (arrow j).continuousPull ⋙ (arrow h).continuousPull ≅ (arrow (h ≫ j)).continuousPull),
  realizationPullLawRationalCompCanonical scalar arrow rationalComp ∧
  ∃ completedComp : (∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left) ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left) ≅
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ j).left),
  realizationPullLawCompletedCompNormalization completedComp ∧
  realizationPullLawCompletedCompUnique completedComp ∧
  realizationPullLawAlphaComp scalar arrow rationalComp completedComp ∧
  ∃ moduleId : (∀ T : RealizationPullScheme l k,
  proEtaleRingModulePullback (𝟙 T.scheme) (rationalCoefficientSheaf l T.scheme E)
      (rationalCoefficientSheaf l T.scheme E) (arrow (𝟙 (Over.mk
        (T.scheme ↘ Spec (.of k))))).rationalCoefficient ≅ 𝟭 _),
  realizationPullLawModuleIdUnit scalar arrow moduleId ∧
  ∃ continuousId : (∀ T : RealizationPullScheme l k,
  (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).continuousPull ≅ 𝟭 _),
  realizationPullLawContinuousIdNormalization scalar arrow moduleId continuousId ∧
  realizationPullLawAlphaId scalar arrow continuousId ∧
  realizationPullLawRawFractions scalar arrow ∧
  ∃ rawUnit : (∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  (arrow h).rationalOrdinary ≅ (arrow h).rationalCompleted),
  realizationPullLawRawUnitIntegral scalar arrow rawUnit ∧
  ∃ rawComp : (∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
  (arrow j).rationalCompleted ⋙ (arrow h).rationalCompleted ≅
    (arrow (h ≫ j)).rationalCompleted),
  realizationPullLawRawCompIntegral scalar arrow completedComp rawComp ∧
  ∃ rawId : (∀ T : RealizationPullScheme l k,
  (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).rationalCompleted ≅ 𝟭 _),
  realizationPullLawRawIdIntegral scalar arrow rawId ∧
  realizationPullLawRawAlphaComp scalar arrow rationalAlpha rationalComp rawComp ∧
  realizationPullLawRawAlphaId scalar arrow rationalAlpha continuousId rawId

/-- Completion-unit-normalized scalar comparison for every morphism over k.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-completed-pull)

Proof:
1. Apply lem-weil-pbc-profinite-coefficient-inverse-image to the finite quotient tower.
Its finite-projection equations identify its map with completedCoefficientMap. Under
continuous integral coordinates, reduction commutes with precomposition, so the map
is precomposition. Continuous coefficient pullback composition supplies coherence.
2. Apply lem-weil-pbc-integral-stratified-perfect-characterization. Pull back each finite
stratum by a fiber product and each trivializing cover by base change. The same perfect
finite-projective complex supplies the local model. Weakly etale and fpqc base-change
stability and the canonical tensor and composition comparisons give every integral
condition, including the uniform reduction bounds and compatible etale origins.
3. Lem-weil-pbc-reduction-pullback-derived-tower identifies the pulled strict quotient
augmentation with that of ordinary pullback. Naturality of the constant-tower adjunction
unit identifies the actual strict completion units, not just their projections. Apply
lem-weil-pbc-intrinsic-to-tower-complete to the ordinary integral pullback from step 2.
4. Use lem-weil-pbc-localization-inverse-image-coherence, with the actual coefficient
map. It identifies continuous rational coefficients with localization, preserves units
and sends each sheaf-local fraction to its pulled numerator with the same denominator.
The normalized module comparison descends on unbounded complexes; its representative
equation is derived_normalization. This gives ordinaryComparison for the scalar functor.
5. Define alpha by ordinaryComparison after F of the inverse strict completion unit.
Its normalization equation is the same formula multiplied by F of that unit. The
module-unit equation gives the localization-unit normalization and fraction formula.
6. Define completedComp by the normalization displayed in the node. Its precomposed
factors are invertible by step 3, giving existence and uniqueness. Their naturality
makes the comparison natural. The identity is the inverse unit followed by the ordinary
identity comparison; it is retained by the equivalent alpha_id equation.
7. Precompose the alpha composition equation with F of the two invertible units.
Naturality moves the inner unit across ordinaryComparison; inverse factors cancel.
The remaining equation is the ordinary localization composition equation. Cancel the
precomposition. The identity calculation is identical with one unit.
8. Prop-weil-pbc-rational-transport extends the actual A-linear restrictions and their
natural transformations to raw rationalizations. Tensoring a Hom with E preserves its
numerator and denominator. Scalar-functor fractions give the displayed rationalAlpha
normalization; identity, composition and unit equations persist by functoriality and
uniqueness of the extension. Objects are unchanged; no idempotent completion is taken. -/
theorem realization_completed_pull (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] :
    RealizationCompletedPullData l E k := by
  sorry

end WeilConjectures
