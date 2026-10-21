/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedDerivedPullbackLinear
import Sheaf.Paper.OrdinaryPullbackStratifiedModels
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Rational realization of the specified completed-pullback unit

Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15,
pp. 50, 54, 62 (blueprint: lem-per-rational-realization-pullback-comparison).

The integral unit is the published strict quotient-tower unit. The ordinary
comparison is fixed on tensor generators and by its derived computation counits.
Its descent retains all raw fraction arrows, without taking a Karoubi envelope.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The scalar-localization map specified by the recorded realization data.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
abbrev rationalPullScalar {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RationalModuleRealization l E T) := s.integralIso.hom ≫ s.inclusion

/-- An actual raw fraction with integral numerator and the given uniformizer power.
Source: Bhatt--Scholze, Section 6.8, scalar localization
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def rationalPullFraction (T : Scheme.{u})
    {K L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)}
    (f : K ⟶ L) (n : ℕ) :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K ⟶
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj L :=
  (IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
    (pbcUniformizer l E)) ^ n •
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f

/-- Ordinary rational ringed pullback with its actual coefficient map, without an
isomorphism assumption on that map. Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
abbrev rationalPullModule {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :=
  proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _) ⋙ pbcExtend c

/-- Unbounded derived rational ringed pullback: exact inverse image followed by
actual derived scalar extension. Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def rationalPullDerived {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :=
  adicTowerPullback g (rationalCoefficientSheaf l T E) ⋙ pbcDerivedExtend c

/-- The ordinary computation counit of that composite on cochain representatives.
Source: Stacks Tag 06YY; Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def rationalPullComplexCounit {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ) :
    (rationalPullDerived l E g c).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((rationalPullModule l E g c).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedExtend c).map
      ((proEtaleRingDerivedPullbackFactors g (rationalCoefficientSheaf l T E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E)) (Iso.refl _)).hom.app P) ≫
    pbcComplexCounit c
      (((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E)) (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Integral preservation and invertibility of exactly the quotient-tower unit.
Membership includes intrinsic completeness, uniform reductions and compatible etale origins.
Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.9
(blueprint: lem-per-rational-realization-pullback-comparison). -/
structure RationalPullIntegral (g : X ⟶ Y) where
  /-- Ordinary coefficient pullback remains in the full integral category. -/
  ordinary_mem : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)
  /-- The completed object belongs to that same category. -/
  completed_mem : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj)
  /-- This is the published unit, with its strict quotient augmentation. -/
  unit_isIso : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)

/-- Restriction keeps the actual strict completed-pullback objects and arrows.
Source: Bhatt--Scholze, Lemma 6.5.9 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def RationalPullIntegral.completedFunctor {g : X ⟶ Y} (a : RationalPullIntegral l E g) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) a.completed_mem

/-- All maps of the comparison, with their tensor, derived and fraction normalizations.
The coefficient map is fixed by its localization unit, without an isomorphism hypothesis.
Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
structure RationalRealizationPullbackComparison (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) where
  /-- The integral preservation and specified-unit assertions. -/
  integral : RationalPullIntegral l E g
  /-- Localization of the canonical integral coefficient map. -/
  rationalCoefficient : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (rationalCoefficientSheaf l Y E) ⟶ rationalCoefficientSheaf l X E
  /-- The ring comparison preserves each inverse-image numerator. -/
  rational_normalization : rationalCoefficientRestrictionNormalized l E g
    rationalCoefficient
  /-- This square fixes the localized coefficient map on its localization unit. -/
  coefficient_square : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (rationalPullScalar l E sY) ≫ rationalCoefficient =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ rationalPullScalar l E sX
  /-- Balanced flattening between the two ordinary module expressions. -/
  moduleComparison : pbcActualModulePull g (pbcIntegralDatum l E) ⋙
      pbcExtend (rationalPullScalar l E sX) ≅
    pbcExtend (rationalPullScalar l E sY) ⋙
      rationalPullModule l E g rationalCoefficient
  /-- On generators this inserts the same numerator and tensor units on either side.
  Linearity determines the balanced tensor maps, including all denominators. -/
  module_unit : ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (moduleComparison.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (rationalPullScalar l E sX)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M V m)) =
    pbcTensorSection rationalCoefficient
      ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l Y E)) (Iso.refl _)).obj
            ((pbcExtend (rationalPullScalar l E sY)).obj M))
      (op ((proEtaleBaseChange g).obj V)) 1
      (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l Y E)) (Iso.refl _)
        ((pbcExtend (rationalPullScalar l E sY)).obj M) V
        (pbcTensorSection (rationalPullScalar l E sY) M (op V) 1 m))
  /-- The ordinary comparison in the unbounded derived categories. -/
  ordinaryComparison : pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
      pbcDerivedExtend (rationalPullScalar l E sX) ≅
    pbcDerivedExtend (rationalPullScalar l E sY) ⋙
      rationalPullDerived l E g rationalCoefficient
  /-- The derived arrow is the localization of the balanced termwise arrow.
  On flat-term K-flat representatives the computation counits are invertible. -/
  derived_normalization : ∀ P : CochainComplex
      (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ,
    ordinaryComparison.hom.app (DerivedCategory.Q.obj P) ≫
        (rationalPullDerived l E g rationalCoefficient).map
            (pbcComplexCounit (rationalPullScalar l E sY) P) ≫
        rationalPullComplexCounit l E g rationalCoefficient
            (((pbcExtend (rationalPullScalar l E sY)).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedExtend (rationalPullScalar l E sX)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit (rationalPullScalar l E sX)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex moduleComparison (.up ℤ)).hom.app P)
  /-- Completed pullback on the raw rationalizations. -/
  rawPull : PbcRationalCategory Y (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
    PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E)
  /-- No objects are added to raw localization. -/
  raw_objects : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    rawPull.obj ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
        ((integral.completedFunctor l E).obj K)
  /-- Every fraction keeps its denominator and applies the actual pullback to its numerator. -/
  raw_fractions : ∀ (K L : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E))
      (f : K ⟶ L) (n : ℕ),
    rawPull.map (rationalPullFraction l E Y f n) = eqToHom (raw_objects K) ≫
      rationalPullFraction l E X ((integral.completedFunctor l E).map f) n ≫
        eqToHom (raw_objects L).symm
  /-- The required natural isomorphism on all raw rational morphisms. -/
  alpha : rawPull ⋙ sX.J ≅ sY.J ⋙
    rationalPullDerived l E g rationalCoefficient
  /-- Equivalently, alpha is F of the inverse specified unit followed by flattening.
  Object equalities are only the recorded formulas J(QK)=F(K) and raw_objects. -/
  alpha_normalization : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    (pbcDerivedExtend (rationalPullScalar l E sX)).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ≫
      eqToHom (sX.objects ((integral.completedFunctor l E).obj K)).symm ≫
      sX.J.map (eqToHom (raw_objects K).symm) ≫ alpha.hom.app
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
      (rationalPullDerived l E g rationalCoefficient).map
          (eqToHom (sY.objects K)) = ordinaryComparison.hom.app K.obj

/-- Ordinary pullback takes each perfect constant model to the same perfect scalar model.
This applies on pulled-back strata and their pro-etale covering charts, without imposing
noetherianity on a chart. Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison).

Proof: represent P by a bounded complex of finite projective A-modules. Its completed
constant realization has flat terms and is K-flat. The ordinary pullback computation
counit therefore is invertible. Termwise balanced tensor flattening sends
b tensor (a tensor p) to b c(a) tensor p, with inverse inserting one. These maps commute
with differentials and the finite-projective idempotents, as in
lem-tw-ordinary-pullback-stratified-models. Localizing gives the asserted model. -/
theorem rationalRealizationPullbackModel {S T : Scheme.{u}} (h : S ⟶ T)
    (P : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (_hP : @DerivedCategory.IsPerfectRingComplex (PbcIntegralRing l E) _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} (PbcIntegralRing l E))) P) :
    Nonempty ((pbcActualDerivedPull h (pbcIntegralDatum l E)).obj
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj P) ≅
      (integralConstantDerived S (pbcIntegralDatum l E)).obj P) := by
  sorry

/-- Rational realization commutes with the specified completed pullback for any morphism.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15,
pp. 50, 54, 62 (blueprint: lem-per-rational-realization-pullback-comparison).

Proof (the seven steps of the node):
1. Apply lem-weil-pbc-integral-stratified-perfect-characterization and
lem-tw-ordinary-pullback-stratified-models. Pull back strata and covers, discarding
empty strata. The same perfect A-complex gives each new local model. Reverse the
characterization to retain completeness, uniform bounds and compatible etale witnesses.
2. Finite coefficient quotients and lem-weil-pbc-profinite-coefficient-inverse-image
identify the projection-defined coefficient map. Apply
lem-weil-pbc-reduction-pullback-derived-tower: its augmentation equation identifies
Rlim(tau) composed with the specified unit with the ordinary object's quotient unit.
This is an equality of induced maps, not an inference from their projections.
lem-weil-pbc-intrinsic-to-tower-complete makes that unit invertible by step 1.
3. Choose a flat-term K-flat resolution by lem-pc-kflat-resolution. The inverse-image,
coefficient-extension and localization operations preserve its resolving class by
lem-weil-pbc-ringed-topos-kflat-pullback. Use
lem-weil-pbc-ringed-topoi-derived-pullback to compute the derived operations.
4. Flatten u tensor (s tensor n) to us tensor n; the inverse inserts one.
5. Use lem-weil-pbc-localization-inverse-image-coherence to identify the pulled
localization with localization of the pulled ring, preserving the unit. Flatten
u tensor (r/varpi^m tensor n) to u c(r) varpi^(-m) tensor n. Both ordinary sides
thus identify with E_X tensor over g inverse B_Y of g inverse K. Sheafify these
balanced maps; their natural chain isomorphism has the stated derived normalization.
6. Compose this comparison with realization of the inverse strict completion unit.
The displayed alpha_normalization is this formula precomposed with realization
of that invertible unit, with the recorded object formulas inserted.
7. The coefficient maps preserve constant A-scalars. Apply
lem-pur-ringed-derived-pullback-linear, then conjugate by the invertible natural
units to obtain A-linearity of completed pullback. Extend f/varpi^n by the same
denominator; the annihilating-power criterion proves independence of representative.
Multiply integral naturality by varpi^(-n), using the realization fraction formula.
This yields the raw natural isomorphism. No coefficient isomorphism is assumed. -/
theorem rationalRealizationPullbackComparison (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) :
    Nonempty (RationalRealizationPullbackComparison l E g sX sY) := by
  sorry

end AlgebraicGeometry.Scheme
