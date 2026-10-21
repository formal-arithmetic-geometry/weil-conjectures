/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Targets.SliceRestrictionStrictDerivedLimit
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Exact integral stratum charts and their pullback square

Source: Bhatt--Scholze, Proposition 6.6.11, Lemmas 6.5.8--6.5.9 and
Remark 6.5.10 (blueprint: lem-a1-integral-stratum-chart-restrictions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures.IntegralStratumCharts

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded integral predicate in the canonical adic presentation.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def constructible (X : Scheme.{u}) :
    ObjectProperty (PbcCompletedDerived X (pbcIntegralDatum l E)) :=
  fun K ↦ sfIntegralConstructible l E X
    ((ImmersionCompletedPullback.transport l E X).obj K)

/-- The canonical ordinary-to-completed map, in the ordinary exact presentation.
Source: Bhatt--Scholze, Remark 6.5.10
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def completionMap {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (ImmersionCompletedPullback.derivedIso l E f).inv ≫
    pbcActualCompletedPullUnit f (pbcIntegralDatum l E)

/-- Exact restriction, its actual coefficient and strict Roos comparisons, and its
normalized identification with the specified integral pullback. The scalar and derived
presentations are those already recorded in the DAG.
Source: Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
structure ExactRestriction {X Y : Scheme.{u}} (f : Y ⟶ X) where
  limits : PreservesLimitsOfSize.{u + 1, u + 1}
    (ImmersionCompletedPullback.modulePull l E f)
  finiteLimits : PreservesFiniteLimits (ImmersionCompletedPullback.modulePull l E f)
  finiteColimits : PreservesFiniteColimits (ImmersionCompletedPullback.modulePull l E f)
  ringProducts : PreservesLimitsOfShape (Discrete ℕ)
    (proEtaleSheafInverseImage f CommRingCat.{u + 1})
  coefficientLimit : PreservesLimit (pbcAdicRings X (pbcIntegralDatum l E))
    (proEtaleSheafInverseImage f CommRingCat.{u + 1})
  coefficients : ∀ n : ℕ,
    ((pbcIntegralDatum l E).integralRingIso f).hom ≫
        (pbcIntegralDatum l E).projection Y n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((pbcIntegralDatum l E).projection X n) ≫
        ((pbcIntegralDatum l E).finiteRingIso f n).hom
  roos : ∀ M : CochainComplex
      (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ,
    ∃! e : (ImmersionCompletedPullback.complexPull l E f).obj (strictRoosComplex M) ≅
        strictRoosComplex ((ImmersionCompletedPullback.towerComplexPull l E f).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates
            ((ImmersionCompletedPullback.towerComplexPull l E f).obj M) p).hom =
        (ImmersionCompletedPullback.modulePull l E f).map
            (strictRoosCoordinates M p).hom ≫
          (ImmersionCompletedPullback.modulePull l E f).biprodComparison _ _ ≫
            biprod.map ((ImmersionCompletedPullback.productComparison l E f M).f p)
              ((ImmersionCompletedPullback.productComparison l E f M).f (p + 1))
  derivedLimit : ∀ T : DerivedCategory ((pbcIntegralDatum l E).towers X),
    IsIso (ImmersionCompletedPullback.rlimComparison l E f T)
  completed : IntegralCompletedComparison.Comparison l E f
  complete : ∀ K : (constructible l E X).FullSubcategory,
    IntegralCompletedComparison.Complete l E K.obj
  comparison : ∀ K : (constructible l E X).FullSubcategory,
    (IntegralCompletedComparison.integral l E f).obj K.obj ≅
      ((pbcIntegralDatum l E).pull f ⋙ ImmersionCompletedPullback.transport l E Y).obj K.obj
  naturality : ∀ (K L : (constructible l E X).FullSubcategory) (a : K ⟶ L),
    (IntegralCompletedComparison.integral l E f).map a.hom ≫ (comparison L).hom =
      (comparison K).hom ≫
        ((pbcIntegralDatum l E).pull f ⋙
          ImmersionCompletedPullback.transport l E Y).map a.hom
  normalization : ∀ K : (constructible l E X).FullSubcategory,
    (comparison K).hom ≫ (ImmersionCompletedPullback.transport l E Y).map
        ((completionMap l E f).app K.obj) =
      (completed.gamma K.obj (complete K)).hom
  preserves : ∀ K : (constructible l E X).FullSubcategory,
    constructible l E Y (((pbcIntegralDatum l E).pull f).obj K.obj)
  cohomology : ∀ j : ℤ,
    Nonempty (DerivedCategory.homologyFunctor
        (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) j ⋙
          ImmersionCompletedPullback.modulePull l E f ≅
      (pbcIntegralDatum l E).pull f ⋙ DerivedCategory.homologyFunctor
        (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) j)

/-- The actual chosen pullback square of a chart and the original morphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4)--(5)
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def chartSquare {X W V : Scheme.{u}} (h : W ⟶ X) (q : V ⟶ X) :
    ChosenCartesianSquare (pullback.fst q h) (pullback.snd q h) q h where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- The finite-coefficient comparison is precisely the two canonical composition maps.
Source: Bhatt--Scholze, Lemma 6.5.9(4)--(5); Stacks 0D6D
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def finiteSquare {X W V : Scheme.{u}} (h : W ⟶ X) (q : V ⟶ X) (n : ℕ) :=
  proEtaleAmbientRingedPullbackComparison (chartSquare h q)
    ((pbcIntegralDatum l E).finiteRing V n) ((pbcIntegralDatum l E).finiteRing X n)
    ((pbcIntegralDatum l E).finiteRing (pullback q h) n)
    ((pbcIntegralDatum l E).finiteRing W n)
    ((pbcIntegralDatum l E).finiteRingIso q n)
    ((pbcIntegralDatum l E).finiteRingIso h n)
    ((pbcIntegralDatum l E).finiteRingIso (pullback.fst q h) n)
    ((pbcIntegralDatum l E).finiteRingIso (pullback.snd q h) n)
    ((pbcIntegralDatum l E).finite_coherent (chartSquare h q) n)

/-- Reduce the left path using the actual quotient projection and exact restriction.
Source: Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def leftReduction {X W V : Scheme.{u}} (h : W ⟶ X) (q : V ⟶ X)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :=
  ((pbcIntegralDatum l E).chi (pullback.snd q h) n).inv.app
      ((completedPullbackFunctor h (pbcIntegralDatum l E)).obj K) ≫
    ((pbcIntegralDatum l E).finitePull (pullback.snd q h) n).map
      (completedPullbackReductionArrow h (pbcIntegralDatum l E) K n)

/-- Reduce the right path with the same actual quotient maps.
Source: Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def rightReduction {X W V : Scheme.{u}} (h : W ⟶ X) (q : V ⟶ X)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :=
  completedPullbackReductionArrow (pullback.fst q h) (pbcIntegralDatum l E)
      (((pbcIntegralDatum l E).pull q).obj K) n ≫
    ((pbcIntegralDatum l E).finitePull (pullback.fst q h) n).map
      (((pbcIntegralDatum l E).chi q n).inv.app K)

/-- A natural chart square, with its finite reductions fixed as maps, not just objects.
Here q is the composite of the stratum immersion and the covering-object map.
Source: Bhatt--Scholze, Lemma 6.5.9(4)--(5)
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
structure PullbackSquare {X W V : Scheme.{u}} (h : W ⟶ X) (q : V ⟶ X) where
  comparison : (constructible l E X).ι ⋙ completedPullbackFunctor h (pbcIntegralDatum l E) ⋙
      (pbcIntegralDatum l E).pull (pullback.snd q h) ≅
    (constructible l E X).ι ⋙ (pbcIntegralDatum l E).pull q ⋙
      completedPullbackFunctor (pullback.fst q h) (pbcIntegralDatum l E)
  reductions : ∀ (K : (constructible l E X).FullSubcategory) (n : ℕ),
    ((pbcIntegralDatum l E).reduction (pullback q h) n).map
          (comparison.hom.app K) ≫ rightReduction l E h q K.obj n =
      leftReduction l E h q K.obj n ≫ (finiteSquare l E h q n).hom.app
        (((pbcIntegralDatum l E).reduction X n).obj K.obj)

/-- Regard the chosen locally closed partition with constructibility as the existing
constructible stratification, in order to use its published pullback construction.
Source: Stacks 09XZ (blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def withConstructible {X : Scheme.{u}} (s : Scheme.FiniteLocallyClosedStratification X)
    (hs : ∀ a, Topology.IsConstructible (s.stratum a)) : Scheme.Stratification X where
  n := s.n
  stratum := s.stratum
  isLocallyClosed_stratum := s.isLocallyClosed_stratum
  iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
  isConstructible_stratum := hs
  domain := s.domain
  immersion := s.immersion
  isImmersion := s.isImmersion
  range_immersion := s.range_immersion

/-- The chart base-change arrow to the actual pulled-back stratum.
Its source is exactly the chosen fibre product of the original chart with W.
Source: Stacks 022D (blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def chartMap {X W S : Scheme.{u}} (h : W ⟶ X) (i : S ⟶ X)
    (U : S.ProEt) : pullback (U.hom ≫ i) h ⟶ pullback i h :=
  pullback.lift (pullback.fst (U.hom ≫ i) h ≫ U.hom)
    (pullback.snd (U.hom ≫ i) h) ((Category.assoc _ _ _).trans pullback.condition)

/-- A bounded finite-projective scalar chart, using the recorded exact ordinary
completed constant realization. Cohomological bounds concern the scalar model,
not the degrees of the finite-projective representative.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
structure Model {X S : Scheme.{u}} (i : S ⟶ X) (U : S.ProEt)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) where
  complex : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ
  lower : ℤ
  upper : ℤ
  boundedBelow : complex.IsStrictlyGE lower
  boundedAbove : complex.IsStrictlyLE upper
  projective : ∀ j : ℤ, Module.Projective (PbcIntegralRing l E) (complex.X j)
  finite : ∀ j : ℤ, Module.Finite (PbcIntegralRing l E) (complex.X j)
  comparison : ((pbcIntegralDatum l E).pull U.hom).obj
      (((pbcIntegralDatum l E).pull i).obj K) ≅
    (integralConstantDerived U.left (pbcIntegralDatum l E)).obj (DerivedCategory.Q.obj complex)
  bounds : ∀ (a b : ℤ),
    (∀ j : ℤ, j ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) →
    ∀ j : ℤ, j ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((integralConstantDerived U.left (pbcIntegralDatum l E)).obj
        (DerivedCategory.Q.obj complex)))

/-- The finite stratification, covering families, chart models and their actual pullbacks.
Empty strata are permitted and introduce no extra nonemptiness hypothesis.
Source: Bhatt--Scholze, Proposition 6.6.11 and Lemmas 6.5.8--6.5.9
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
structure Charts {X W : Scheme.{u}} (h : W ⟶ X)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) where
  strata : Scheme.FiniteLocallyClosedStratification X
  constructibleStrata : ∀ a, Topology.IsConstructible (strata.stratum a)
  index : Fin strata.n → Type (u + 1)
  object : ∀ a, index a → (strata.domain a).ProEt
  covering : ∀ a,
    Sieve.ofArrows (object a) (fun t ↦ terminal.from (object a t)) ∈
      ProEt.topology (strata.domain a) (⊤_ (strata.domain a).ProEt)
  stratumRestriction : ∀ a, ExactRestriction l E (strata.immersion a)
  objectRestriction : ∀ a t, ExactRestriction l E (object a t).hom
  chartRestriction : ∀ a t,
    ExactRestriction l E ((object a t).hom ≫ strata.immersion a)
  model : ∀ a t, Model l E (strata.immersion a) (object a t) K
  pulledStratumRestriction : ∀ a,
    ExactRestriction l E (pullback.snd (strata.immersion a) h)
  pulledWeaklyEtale : ∀ a t, WeaklyEtale (chartMap h (strata.immersion a) (object a t))
  pulledCovering : ∀ a,
    Sieve.ofArrows
      (fun t ↦ @Scheme.ProEt.mk _ _
        (chartMap h (strata.immersion a) (object a t)) (pulledWeaklyEtale a t))
      (fun t ↦ terminal.from (@Scheme.ProEt.mk _ _
        (chartMap h (strata.immersion a) (object a t)) (pulledWeaklyEtale a t))) ∈
      ProEt.topology (pullback (strata.immersion a) h)
        (⊤_ (pullback (strata.immersion a) h).ProEt)
  pulledObjectRestriction : ∀ a t,
    ExactRestriction l E (chartMap h (strata.immersion a) (object a t))
  pulledChartRestriction : ∀ a t,
    ExactRestriction l E (pullback.snd ((object a t).hom ≫ strata.immersion a) h)
  chartPullback : ∀ a t, IntegralCompletedComparison.Comparison l E
    (pullback.fst ((object a t).hom ≫ strata.immersion a) h)
  square : ∀ a t, PullbackSquare l E h ((object a t).hom ≫ strata.immersion a)

/-- The actual finite constructible stratification on W. Empty inverse-image strata
may be omitted; keeping them has no effect on the partition or the chart conditions.
Source: Stacks 09XZ, 022D; Bhatt--Scholze, Lemma 6.5.9
(blueprint: lem-a1-integral-stratum-chart-restrictions). -/
def Charts.pulledStrata {X W : Scheme.{u}} {h : W ⟶ X}
    {K : PbcCompletedDerived X (pbcIntegralDatum l E)} (C : Charts l E h K) :
    Scheme.Stratification W :=
  (withConstructible C.strata C.constructibleStrata).pullback h

/-- Exact integral restriction charts and their pullback square.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemmas 6.5.8--6.5.9 and Remark 6.5.10
(blueprint: lem-a1-integral-stratum-chart-restrictions).

Proof:
1. Integral-stratified-perfect-characterization identifies the recorded detailed category
with stratified perfect objects. On each stratum choose a pro-etale trivializing cover
and a bounded finite-projective representative. Its constant terms are flat, so
bounded-above-flat-kflat-site identifies ordinary scalar extension with derived extension.
Noetherian affine pieces have Noetherian underlying spaces; every open there is compact,
so the locally closed strata are constructible.
2. Proetale-immersion-limit-preservation and immersion-completed-pullback-comparison
provide exact ordinary stratum restriction, its coefficient identification and its
finite projections. Compose its inverse completion unit with the normalized gamma of
integral-pullback-completed-comparison.
3. Proetale-object-inverse-image-restriction identifies covering-object inverse image
with slice restriction. Site-restriction-module-adjunction-exact gives exactness and
limit preservation. Adic-stratum-completion-unit preserves completeness and finite
reductions without assuming the chart scheme Noetherian.
4. Slice-restriction-strict-derived-limit and roos-additive-comparison commute with
strict Roos models: each product projection intertwines the pulled-back transition;
apply that same product comparison in both cone coordinates. This fixes the maps
and all finite quotient projections, naturally in strict tower maps.
5. Local-derived-restriction-comparisons gives cohomology compatibility. Restricting
vanishing cohomology gives the identical interval for the scalar chart model.
6. Constructible-pullback-stratification gives the actual fibre-product strata, with
preimage images and disjointness. The same Noetherian argument makes them constructible.
Weakly-etale-composition-base-change and fpqc-covering-base-change give the pulled covers.
7. Integral-operations-preserve-constructible gives constructibility of the specified
pullback and of chart restrictions. Apply steps 2--4 on W for the primed restrictions.
8. Integral-pullback-composition along the two factorizations of the chart square gives
the natural comparison. Its finite normalization, together with the projection-preserving
restriction comparisons, gives exactly the reductions equation in PullbackSquare.
9. Integral-pullback-completed-comparison identifies the specified pullback with the
strict completed pullback. Completed-pullback-triangles transports shifts and triangles
through gamma, with the comparison's stated shift square. Finite inverse image, products,
1-s and both cone coordinates commute with constant scalar multiplication, giving
R-linearity. This is exactness on constructible objects, not global t-exactness.
-/
theorem integral_stratum_chart_restrictions {X W : Scheme.{u}} (h : W ⟶ X)
    [IsNoetherian X] [IsNoetherian W]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hWdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hXl : IsUnit (l : Γ(X, ⊤))) (_hWl : IsUnit (l : Γ(W, ⊤))) :
    (∀ K : (constructible l E X).FullSubcategory, Nonempty (Charts l E h K.obj)) ∧
    (∀ K : (constructible l E X).FullSubcategory,
      sfIntegralConstructible l E W ((IntegralCompletedComparison.integral l E h).obj K.obj)) ∧
    ∃ c : IntegralCompletedComparison.Comparison l E h,
      (integralDerivedPullback l E h).Additive ∧
      (∀ (a : Padic.coefficientExtensionIntegers l E)
        (K L : (constructible l E X).FullSubcategory) (f : K ⟶ L),
        (integralDerivedPullback l E h).map
            ((integralScalarDerivedAction l E X a).app
              ((ImmersionCompletedPullback.transport l E X).obj K.obj) ≫
                (ImmersionCompletedPullback.transport l E X).map f.hom) =
          (integralScalarDerivedAction l E W a).app
              ((IntegralCompletedComparison.integral l E h).obj K.obj) ≫
            (IntegralCompletedComparison.integral l E h).map f.hom) ∧
      (fun [shift : (integralDerivedPullback l E h).CommShift ℤ] ↦
        ∀ T : Triangle (DerivedCategory (integralTowerModules l E X)),
          T ∈ distTriang _ →
          sfIntegralConstructible l E X T.obj₁ →
          sfIntegralConstructible l E X T.obj₂ →
          sfIntegralConstructible l E X T.obj₃ →
          (integralDerivedPullback l E h).mapTriangle.obj T ∈ distTriang _)
        (shift := c.derivedShift) := by
  sorry

end WeilConjectures.IntegralStratumCharts
