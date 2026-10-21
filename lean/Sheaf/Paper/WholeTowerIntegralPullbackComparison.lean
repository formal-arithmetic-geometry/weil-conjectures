/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.FdCoefficientComparisonSystem
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralPullbackShiftCoordinates
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization
import Sheaf.TraceFormula.CounitRealizationSubstitution
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.SpecifiedPullbackComparisonAlpha
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.ExactProductFunctorRoosDescent
import Sheaf.Paper.QuotientSystemMixedCoherence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Simultaneous normalized integral pullback comparison

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; the auxiliary whole-tower subclaim
extracted from the coefficient-category comparison, steps 7--8
(blueprint: lem-fd-whole-tower-integral-pullback-comparison).

The finite datum has the inverse orientation to b in the node. Its chain field
and normalization retain the actual quotient maps and zero shifted coordinate.
The realization system retains the K-injective-normalized Roos map and the
whole-system counits. The scalar equation below is integral, before localization;
the mixed field of each pullback system records its raw rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The coefficient transport uses the canonical exact-functor shift.
Source: trace-definition auxiliary whole-tower subclaim; Stacks 014E
(blueprint: lem-fd-whole-tower-integral-pullback-comparison). -/
instance fdWholeTowerTransportShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (integralDetailedTransport T l E).CommShift ℤ :=
  inferInstanceAs ((fdCoefficientTransport l E T).mapDerivedCategory.CommShift ℤ)

/-- Simultaneous choices for the normalized comparison. All coefficient and scheme
indices are quantified together; the integral datum is b inverse. Source: trace-definition
final sentence, auxiliary whole-tower subclaim; Stacks 099N and 0941
(blueprint: lem-fd-whole-tower-integral-pullback-comparison). -/
structure FdWholeTowerIntegralComparison
    (C : ∀ (T : Scheme.{u}) [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))],
      FdCoefficientComparison l Ω T) where
  /-- The normalized whole-diagram realization, with its retained counits. -/
  realization : IntegralComparisonSystem.{u} l
  /-- All fields and inclusions use this same realization system. -/
  realization_coherent : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L),
    IntegralComparisonRealizationCoherence l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) realization
  /-- The inverse b, its ambient lift, actual unit-section chain map, and raw localization.
  The mixed field is the rational scalar square with the specified inverse chi maps. -/
  pullback : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T), FdPullbackSystem l Ω (C U) (C T) h
  /-- Identity compatibility with the specified whole-system and actual PBC units. -/
  unit : ∀ (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω),
    ∃ su : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (𝟙 T) ≅ 𝟭 _,
    ∃ pu : fdPbcIntegralPull l Ω (𝟙 T) E ≅ 𝟭 _,
      (∀ K, (su.hom.app K).hom =
        (integralComparisonUnit l (pbcFiniteField.{u} l Ω E) realization T K).hom) ∧
      (∀ K, HEq (pu.hom.app K).hom
        ((pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Ω E) T).hom.app
          ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((pullback (Iso.refl T)).finite E).integral.hom.app K ≫
          ((C T).stage E).integral.functor.map (su.hom.app K) =
        pu.hom.app (((C T).stage E).integral.functor.obj K))
  /-- Composition compatibility, with both compositors fixed independently of b. -/
  composition : ∀ (U V T : Scheme.{u})
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∀ t : V, IsUnit (l : V.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ V) (k : V ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
    ∃ sc : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (h.hom ≫ k.hom) ≅
        constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k.hom ⋙
          constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom,
    ∃ pc : fdPbcIntegralPull l Ω (h.hom ≫ k.hom) E ≅
        fdPbcIntegralPull l Ω k.hom E ⋙ fdPbcIntegralPull l Ω h.hom E,
      (∀ K, (sc.hom.app K).hom =
        (integralComparisonComposition l (pbcFiniteField.{u} l Ω E) realization
          h.hom k.hom K).hom) ∧
      (∀ K, HEq (pc.hom.app K).hom
        ((pbcActualCompletedPullCompIso h.hom k.hom
          (pbcStageDatum.{u} l Ω E)).inv.app ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((pullback (h ≪≫ k)).finite E).integral.hom.app K ≫
          ((C U).stage E).integral.functor.map (sc.hom.app K) =
        pc.hom.app (((C T).stage E).integral.functor.obj K) ≫
          (fdPbcIntegralPull l Ω h.hom E).map
            (((pullback k).finite E).integral.hom.app K) ≫
          ((pullback h).finite E).integral.hom.app
            ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k.hom).obj K))
  /-- The scalar alpha is precisely lambda followed by mu inverse, retaining chi. -/
  scalar_realization : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
    (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom K).hom.hom =
      (integralComparisonScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω e) realization h.hom K).hom
  /-- The integral mixed square, in the inverse-b orientation. The coefficient datum's
  chi field fixes both scalar identifications by the actual completion chain map. -/
  integral_scalar : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
    ∃ alpha : pbcAmbientScalarExtension l Ω T e ⋙
        pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L) ≅
      pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω U e,
    HEq alpha.hom
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom).hom ∧
    HEq
      ((pbcAmbientScalarExtension l Ω U e).map
          (((pullback h).finite E).ambient.hom.app K) ≫
        ((C U).integral_scalar e).hom.app
          ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom).obj K) ≫
        (integralDetailedTransport U l (pbcFiniteField.{u} l Ω L)).map
          (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom K).hom.hom)
      (alpha.inv.app
          ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj) ≫
        (pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L)).map
          (((C T).integral_scalar e).hom.app K) ≫
        ((pullback h).finite L).ambient.hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T).obj K))

  /-- The shift is the signed cone shift, descended through the specified representative
  comparison; the same ambient comparison commutes with it for every integer. -/
  shifts : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
    ∃ c : (integralOperationsPullbackComplexFunctor l
      (pbcFiniteField.{u} l Ω E) h.hom).CommShift ℤ,
    ∃ d : (integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom).CommShift ℤ,
      IntegralCompletedComparison.ShiftCoordinates l (pbcFiniteField.{u} l Ω E) h.hom c ∧
      IntegralCompletedComparison.ShiftDescent l (pbcFiniteField.{u} l Ω E) h.hom c d ∧
      (fun [_sd : (integralDerivedPullback l
          (pbcFiniteField.{u} l Ω E) h.hom).CommShift ℤ] ↦
        ∀ (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) (r : ℤ),
        ∃ hKr : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T (K.obj⟦r⟧),
        HEq
          (((pullback h).finite E).ambient.hom.app ⟨K.obj⟦r⟧, hKr⟩ ≫
            ((integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom ⋙
              integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).commShiftIso
                r).hom.app K.obj)
          (((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
              pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E)).commShiftIso
                r).hom.app K.obj ≫
            (((pullback h).finite E).ambient.hom.app K)⟦r⟧')) (_sd := d)

/-- The normalized whole-tower integral comparison exists simultaneously for all allowed
schemes, all scheme isomorphisms and all finite coefficient fields.
Source: blueprint main-20261015, trace-definition final sentence, auxiliary whole-tower
subclaim; Stacks 099N(2),(5), 0941 and 0D6D
(blueprint: lem-fd-whole-tower-integral-pullback-comparison).

Proof (the eleven steps of the node):
1. Identify completed coefficient sheaves and the full integral categories by
   integralStratifiedPerfectCharacterization. For an isomorphism, inverse image is an
   exact reindexing equivalence preserving limits. ScalarExtensionRingIso identifies module
   pullback with this exact inverse image. Exact functor factorization computes its tower
   derivation termwise. The two pullbacks therefore use the identical strict quotient tower,
   including transitions; no K-flatness of its quotients over the completion is required.
2. Exact countable products and strictRoosComparison identify its product cone with total
   derived limit. For Q to I the comparison is H(q) followed by the inverse of the localized
   inclusion lim I to H(I), z to (0,z). Insert the defining realization identifications.
3. IntegralOperationsWellDefined and strict Roos naturality identify these maps under every
   change of representative, resolution and refinement. Localization uniqueness extends
   naturality to derived morphisms. Preservation of constructibility restricts the comparison.
4. The quotient augmentations gamma_n commute strictly with all transitions. Consequently
   Gamma=(0,(gamma_n)) is a chain map. Roos augmentation normalization says b Gamma is the
   actual PBC completion unit. ConstantTowerNormalization retains its universal counit.
   Inverting b gives exactly the finite datum's ambient normalization and chain field;
   raw localization gives its rational field, on every integral representative.
5. Choose one simultaneous integralPullbackComparisonRealization system. Its whole-system
   counit on a K-injective is the ordinary compatible limit cone. CounitRealizationSubstitution
   retains these counits in every finite word, including all intermediate complete objects.
6. The coefficient ring is a DVR and hence Noetherian. Transport completedPullbackAdjunction
   through ConstantCompletion.equivalence. Under its Hom bijection the actual PBC compositor,
   precomposed with completion units, is ordinary termwise composition. For isomorphisms
   these units are invertible, so this normalization determines the PBC compositor uniquely.
7. Write kappa_p=b kappa_s. Substitute this into the source and target unit/composition
   normalization equations, use naturality of b at kappa_s, and cancel the invertible
   kappa_s. This gives the two asserted integral equations with the specified compositors.
8. FiniteFreeCompletedScalarComparison fixes chi by quotient and zero coordinates. The
   strict map d in specifiedPullbackComparisonAlpha gives alpha_s=F_L(chi) delta_s chi^-1.
   K-flat scalar normalization and finite-free strict-tower transport identify delta_p with
   the actual PBC comparison. The source lambda chi and mu F_L(chi) delta_s are induced by
   the same augmented quotient projection followed by d, so Roos augmentation identifies
   alpha_s with the specified lambda/mu realization.
9. Apply exactProductFunctorRoosDescent to finite-free ordinary scalar extension. Its
   product and limit comparisons retain the universal units. Whole-tower naturality at d
   gives b_L delta_s=delta_p C(b_E), before any individual evaluation.
10. Substitute alpha_s, use naturality at chi and cancel its inverse. This gives
    integral_scalar below. Raw localization preserves composition and inverses, giving
    j=chi^-1 and the mixed square, which is recorded by FdPullbackSystem.mixed.
11. The signed cone shift sends (y,x) to ((-1)^r y,x), fixing (0,z). Thus b commutes
    with the specified shifts. QuotientSystemMixedCoherence gives units, repeated fields,
    coefficient towers and arbitrary finite compositions before realization. Substitute
    the normalized realizations and cancel adjacent comparison/inverse pairs. Localization
    preserves these equalities. No finite Tor-amplitude hypothesis is used. -/
theorem wholeTowerIntegralPullbackComparison (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (C : ∀ (T : Scheme.{u}) [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))],
      FdCoefficientComparison l Ω T) :
    Nonempty (FdWholeTowerIntegralComparison l Ω C) := by
  sorry

end WeilConjectures
