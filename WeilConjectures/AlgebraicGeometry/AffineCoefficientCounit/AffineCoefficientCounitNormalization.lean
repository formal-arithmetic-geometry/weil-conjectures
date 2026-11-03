/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitMaps
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import all WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunction
import all WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Finite affine coefficient domains and normalized counits

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement, finite-coefficient realization and tensor reassociation
(blueprint: lem-pur-affine-coefficient-counit-normalization).

The affine tower is the recorded coordinate model, with literal identity at dimension zero.
The coefficient is the actual right-adjoint image of the unit in the ordered line tower;
affineLinearCoefficientDescent identifies it with A(d)[2d]. Its trace is the actual tower
counit transported by affineLinearCompactComparison, the normalization used by vector
integration on the standard frame. No additional orientation or adjunction is chosen.

## Main definitions
* FiniteAffineNormalization records the coefficient domains and actual tensor equation.
* finiteLineCounit and finiteLineTrace are the actual counit and restricted trace.
* LineCompatibility records the ordinary equation and its specified site transpose.

## Main statements
* affine_coefficient_counit_normalization supplies all affine coefficient domains.
* affine_line_counit_normalization identifies the normalized counit and its transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineCoefficientCounit
open AffineLinePurity VectorIntegrationSite

/-- The ordinary canonical projection domain, cached before coefficient specialization.
Source: projection-domain clause
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def OrdinaryProjectionDomain (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) : Prop :=
  IsIso (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app L).app H)

/-- The specified pro-etale projection domain, cached before coefficient specialization.
Source: projection-domain clause
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def ComparedProjectionDomain (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) : Prop :=
  AffineLinePurity.ProjectionInvertible A (HasCompactification.compactification f)
    ((comparison A X).obj L) ((comparison A Y).obj H)

/-- Invertibility of the integration transpose at the unit.
Source: P at the constant coefficient is the affine purity isomorphism
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def UnitTransposeInvertible (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj L ⟶ 𝟙_ _) :
    Prop :=
  IsIso ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv
    L (𝟙_ _) t)

/-- Both specified projection domains for the actual dualizing object.
Source: the (omega,K) domain clause
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def DualizingProjectionDomain (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (H : Etale.DerivedCategoryModule A Y) : Prop :=
  OrdinaryProjectionDomain A f (Etale.dualizingComplex A f) H ∧
  ComparedProjectionDomain A f (Etale.dualizingComplex A f) H

/-- The exact tensor-transpose equation in ordinary comparison coordinates.
Source: theta composed with tensor of P equals P with coefficients
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def TensorEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj L ⟶ 𝟙_ _) :
    Prop :=
  letI := Etale.derivedBraidedCategory A X
  letI := Etale.derivedBraidedCategory A Y
  letI := Etale.isIso_projectionMap_of_finite A f
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)).map
      ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv L
        (𝟙_ _) t) ≫ (β_ _ _).hom ≫ Etale.dualizingComplexTensorMap A f H =
    (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ H
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (β_ _ L).hom ≫
        ((inv (Etale.projectionMap (ModuleCat.{u + 1} A) f)).app L).app H ≫
        (β_ _ H).hom ≫ ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).map t ≫
        (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y H).hom)

/-- The coefficient-source and projection domains at every coordinate projection.
The quantified pullbacks, twists and shifts are the actual operations, with arbitrary
nonnegative Tate powers and signed shifts. The compactification is retained explicitly.
Source: the two coefficient-domain paragraphs
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def Domains (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (H : Etale.DerivedCategoryModule A Y) : Prop :=
  (∀ (d c : ℕ) (s a b : ℤ),
    Etale.DerivedCategory.hasTorAmplitudeIn A Y a b H →
    Etale.DerivedCategory.isBoundedConstructible A (affineTraceTower Y d)
      ((((Etale.derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower Y d)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).mapDerivedCategory.obj
          H)).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower Y d) N A hA c)))⟦s⟧) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A (affineTraceTower Y d) (a - s) (b - s)
      ((((Etale.derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower Y d)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).mapDerivedCategory.obj
          H)).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower Y d) N A hA c)))⟦s⟧)) ∧
  (∀ d : ℕ,
    Etale.DerivedCategory.isBoundedConstructible A (affineTraceTower Y d)
      (coefficient A N hA Y d)) ∧
  (∀ d b : ℕ,
    Etale.DerivedCategory.isBoundedConstructible A (affineTraceTower Y d)
      (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower Y d) b) ∧
    Etale.DerivedCategory.isBoundedConstructible A (affineTraceTower Y d)
      ((Etale.affineTraceLineLeft A (affineTraceTower Y d)).obj
        ((Etale.affineTraceLineRight A N hA (affineTraceTower Y d)).obj
          (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower Y d) b)))) ∧
  (∀ d : ℕ,
    IsNoetherian (affineTraceTower Y d) ∧
    ∃ e : ℕ, topologicalKrullDim (affineTraceTower Y d) ≤ (e : WithBot ℕ∞)) ∧
  (∀ (d b c : ℕ) (s : ℤ),
    letI : IsNoetherian (affineTraceTower Y d) := affineTraceNoetherian Y d
    OrdinaryProjectionDomain A
      (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)
      (Etale.affineLinearBaseCoefficient A N hA
        (AffineSpace PUnit.{u + 1} (affineTraceTower Y d)) b)
      ((((Etale.derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower Y d)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).mapDerivedCategory.obj
          H)).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower Y d) N A hA c)))⟦s⟧) ∧
    ComparedProjectionDomain A
      (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)
      (Etale.affineLinearBaseCoefficient A N hA
        (AffineSpace PUnit.{u + 1} (affineTraceTower Y d)) b)
      ((((Etale.derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower Y d)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).mapDerivedCategory.obj
          H)).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower Y d) N A hA c)))⟦s⟧)) ∧
  (∀ (d : ℕ) (C : Compactification (affineTraceProjection Y d)),
    IsProjective C.g → IsNoetherian C.Z ∧ ∃ e : ℕ, topologicalKrullDim C.Z ≤ (e : WithBot ℕ∞)) ∧
  (∀ d : ℕ,
    OrdinaryProjectionDomain A (affineTraceProjection Y d)
      (coefficient A N hA Y d) H ∧
    ComparedProjectionDomain A (affineTraceProjection Y d)
      (coefficient A N hA Y d) H ∧
    DualizingProjectionDomain A (affineTraceProjection Y d) H)

/-- Theta composed with tensor of P equals the integration-defined P with coefficients.
These are the canonical comparison coordinates of the constructible pro-etale maps,
using the signed symmetry followed by dualizingComplexTensorMap, and the explicit
adjoint transpose of inverse projection followed by tensor with the trace. The inverse projection is
always the actual specified projection component, rather than an arbitrary isomorphism.
Source: displayed tensor identity and its canonical Tate/shift reassociation
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def TensorNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (H : Etale.DerivedCategoryModule A Y) : Prop :=
  ∀ d : ℕ,
    UnitTransposeInvertible A (affineTraceProjection Y d) (coefficient A N hA Y d)
      (trace A N hN hA Y hY d) ∧
    TensorEquation A (affineTraceProjection Y d) (coefficient A N hA Y d) H
      (trace A N hN hA Y hY d)

/-- The conjunction of all finite affine coefficient-domain and tensor clauses.
Source: the first three paragraphs of the node
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def FiniteAffineNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (ell : ℕ) [Fact ell.Prime] (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : ∀ r : ℕ, IsUnit ((ell ^ (r + 1) : ℕ) : Γ(Y, ⊤)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    Prop :=
  (∃ H : Etale.DerivedCategoryModule A Y,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y H ∧
    Nonempty ((comparison A Y).obj H ≅ K) ∧
    ∀ a b : ℤ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y a b K ↔
      Etale.DerivedCategory.hasTorAmplitudeIn A Y a b H) ∧
  (∀ (H : Etale.DerivedCategoryModule A Y)
    (_hH : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y H)
    (_eH : (comparison A Y).obj H ≅ K)
    (r : ℕ) (hA : ((ell ^ (r + 1) : ℕ) : A) = 0),
    Domains A (ell ^ (r + 1)) hA Y H ∧
    TensorNormalization A (ell ^ (r + 1))
      (pow_pos (Fact.out : ell.Prime).pos _) hA Y (hY r) H)

section LineNormalizationProof

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] CoordinateLine.right AffineLinePurity.ordinarySourceObject
  affineTraceLineCompactification Etale.affineTraceOpenLeft
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar sfFiniteExceptionalAt
  Etale.ordinaryFiniteP1Right Etale.ordinaryFiniteTwistedPullback
  Etale.affineTraceOpenAdjunction Etale.ordinaryFinitePullback Etale.ordinaryFiniteTensor
  constantSheaf GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
  Etale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  Etale.derivedTensorRightDerivedLowerStar
  Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar

set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 1600000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
set_option maxHeartbeats 4000000 in
-- Canonical derived-functor source comparisons require explicit cached-coordinate matching.
end LineNormalizationProof

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

set_option maxHeartbeats 800000 in
-- The retained Hom chain contains several derived-functor comparison types.
attribute [local irreducible] Adjunction.ofIsLeftAdjoint Adjunction.homEquiv
  Functor.rightAdjoint fixedCompactSupportComparisonIso specifiedExceptionalHomEquiv
  derivedComparisonAdjunction


set_option maxHeartbeats 800000 in
-- Comparing the retained source witnesses elaborates the specified derived Hom chain.
end AlgebraicGeometry.ProEtale.AffineCoefficientCounit
