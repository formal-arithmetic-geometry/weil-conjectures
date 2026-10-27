/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteRestrictionCoefficientCore

/-!
# Geometric finite restriction comparisons

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; the finite-stalk
step of the blueprint finite pushforward proof (blueprint:
def-zl-finite-restriction-geometric-comparisons).

## Main definitions

- `WeilConjectures.FiniteRestrictionCoefficient.Geometry`: geometric finite restriction comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.FiniteRestrictionCoefficient
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage integralTransition transition stageSystem)
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {W W' : Scheme.{u}} (g : W' ⟶ W)

/-- Constructible preservation for the already defined completed integral pullback.
Source: Stacks 099N; Bhatt--Scholze 6.8.15
(blueprint: def-zl-finite-restriction-geometric-comparisons). -/
structure PullbackDiagram where
  preserves : ∀ (A : Index l Ω) (K : IntegralStage l Ω W A),
    sfIntegralConstructible l (Coefficient.{u} l Ω A) W'
      ((integralDerivedPullback l (Coefficient.{u} l Ω A) g).obj K.obj)

variable {l Ω g}
/-- The actual full-subcategory restriction of completed integral pullback.
Source: Stacks 099N (blueprint: def-zl-finite-restriction-geometric-comparisons). -/
def PullbackDiagram.functor (P : PullbackDiagram l Ω g) (A : Index l Ω) :
    IntegralStage l Ω W A ⥤ IntegralStage l Ω W' A :=
  (sfIntegralConstructible l (Coefficient.{u} l Ω A) W').lift
    ((sfIntegralConstructible l (Coefficient.{u} l Ω A) W).ι ⋙
      integralDerivedPullback l (Coefficient.{u} l Ω A) g) (P.preserves A)

variable (l Ω g)
set_option genSizeOf false in
set_option genInjectivity false in
/-- Pullback comparisons with their actual completion-unit normalization, and raw
rational descent on the fixed stages. This includes ramified field inclusions.
Source: Bhatt--Scholze 6.8.14, 6.8.15; Stacks 099N
(blueprint: def-zl-finite-restriction-geometric-comparisons). -/
structure PullbackComparisons where
  integral : PullbackDiagram l Ω g
  beta : ∀ (A B : Index l Ω) (h : A ≤ B),
    integral.functor A ⋙ integralTransition l Ω W' A B h ≅
      integralTransition l Ω W A B h ⋙ integral.functor B
  rational : (stageSystem l Ω W).Morphism (stageSystem l Ω W')

attribute [local irreducible] PullbackDiagram.functor
  sfConstructibleIntegralScalarExtension HasDerivedCategory.standard
  scalarPullbackCompleted integralDerivedPullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The scalar comparison is precisely the normalized completed tensor/pullback
comparison. Its rationalization uses the literal integral object and tensor-Hom maps.
Source: Bhatt--Scholze 6.8.14, 6.8.15; Stacks 099N
(blueprint: def-zl-finite-restriction-geometric-comparisons). -/
def PullbackComparisons.Normalized (P : PullbackComparisons l Ω g) : Prop :=
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω W A),
    HEq ((P.beta A B h).hom.app K).hom
      (scalarPullbackCompleted l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
        (coefficientInclusion l Ω A B h) g K.obj K.property.1
        (P.integral.preserves A K).1).hom) ∧
  (∀ (A : Index l Ω) (K : Stage l Ω W A),
    (P.rational.Φ A).obj K = ⟨(P.integral.functor A).obj K.obj⟩) ∧
  (∀ (A : Index l Ω) (K M : IntegralStage l Ω W A)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω A)))
    (g : K ⟶ M),
    HEq ((P.rational.Φ A).map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω A)] g :
        (localization l Ω W A).obj K ⟶ (localization l Ω W A).obj M))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω A)]
        (P.integral.functor A).map g :
          (localization l Ω W' A).obj ((P.integral.functor A).obj K) ⟶
            (localization l Ω W' A).obj ((P.integral.functor A).obj M))) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω W A),
    HEq ((P.rational.β h).hom.app ((localization l Ω W A).obj K))
      ((localization l Ω W' B).map ((P.beta A B h).hom.app K)))

variable {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Every geometric functor used by the finite fibre diagram, with its existing
strict direct-image reconstruction and the completed pullbacks, is retained.
Source: Bhatt--Scholze 6.8.14, 6.8.15; Stacks 0959, 03QP
(blueprint: def-zl-finite-restriction-geometric-comparisons). -/
structure Geometry where
  image : SfStrictDirectImageScalar.IntegralComparisons l Ω f
  fibreImage : SfStrictDirectImageScalar.IntegralComparisons l Ω (pullback.snd f y)
  rationalImage : SfStrictDirectImageScalar.Comparisons l Ω f image
  rationalFibreImage : SfStrictDirectImageScalar.Comparisons l Ω (pullback.snd f y) fibreImage
  pointPull : PullbackComparisons l Ω y
  fibrePull : PullbackComparisons l Ω (pullback.fst f y)
  structurePull : PullbackComparisons l Ω (pullback.snd f y)
  liftPull : ∀ x : FiniteCounitTowers.Points f y,
    PullbackComparisons l Ω (FiniteCounitTowers.lift f y x)
  pointComponent : ∀ x : FiniteCounitTowers.Points f y, PullbackComparisons l Ω x.val

/-- All geometric comparisons have the published unit and tensor normalizations.
Source: Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: def-zl-finite-restriction-geometric-comparisons). -/
def Geometry.Normalized (G : Geometry l Ω f y) : Prop :=
  SfStrictDirectImageScalar.HasIntegralLaws l Ω f G.image ∧
  SfStrictDirectImageScalar.HasIntegralLaws l Ω (pullback.snd f y) G.fibreImage ∧
  SfStrictDirectImageScalar.HasComparisonLaws l Ω f G.image G.rationalImage ∧
  SfStrictDirectImageScalar.HasComparisonLaws l Ω (pullback.snd f y)
    G.fibreImage G.rationalFibreImage ∧
  G.pointPull.Normalized ∧ G.fibrePull.Normalized ∧ G.structurePull.Normalized ∧
  (∀ x, (G.liftPull x).Normalized ∧ (G.pointComponent x).Normalized)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Endpoints identify the actual strict-system diagram with the geometric
composites. The point target is a limiting finite fan, hence also the finite
biproduct; its empty case is the zero object. Comparisons are natural in K.
Source: Stacks 0959, 03QP; Bhatt--Scholze 6.8.15
(blueprint: def-zl-finite-restriction-geometric-comparisons). -/
structure Endpoints (G : Geometry l Ω f y) (I : IntegralComparisons l f y Ω) where
  source : ∀ A : Index l Ω, (I.diagram A).functor .source ≅
    (G.image.integral A).image ⋙ G.pointPull.integral.functor A
  middle : ∀ A : Index l Ω, (I.diagram A).functor .middle ≅
    G.fibrePull.integral.functor A ⋙ (G.fibreImage.integral A).image
  projection : ∀ (A : Index l Ω) (x : FiniteCounitTowers.Points f y),
    (I.diagram A).functor .target ⟶ (G.pointComponent x).integral.functor A
  limit : ∀ A : Index l Ω,
    IsLimit (Fan.mk ((I.diagram A).functor .target) (projection A))
  empty : IsEmpty (FiniteCounitTowers.Points f y) →
    ∀ (A : Index l Ω) (K : IntegralStage l Ω X A),
      IsZero (((I.diagram A).functor .target).obj K)


end WeilConjectures.FiniteRestrictionCoefficient
