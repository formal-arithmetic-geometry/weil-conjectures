/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounitMaps
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSiteComparison
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
import WeilConjectures.AlgebraicGeometry.CoordinateLineAdjunction
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

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

/-- Finite affine coefficient origins, exact Tor windows, projection domains, and the
normalized tensor equation at every dimension and annihilating exponent.
Source: main-20261015, projection-purity agreement, finite coefficient calculation
(blueprint: lem-pur-affine-coefficient-counit-normalization).

Proof:
1. Choose a Tor interval of K. det-pe-finite-tor-comparison-noetherian gives a bounded
constructible ordinary origin and preserves and reflects that same interval. Finite type
makes Y Noetherian and qcqs; the coefficient quotient is finite and Noetherian.
2. lem-sf-pullback-tor-amplitude preserves the interval under each coordinate pullback;
prop-weil-twist-preserves preserves it under a finite locally free Tate line. A signed
shift s replaces [a,b] by [a-s,b-s]. Iterate these operations for every base factor.
The shifted Tate coefficients and their products are bounded constructible.
3. lem-amb-affine-space-top-trace at dimension one identifies the line compact-support
source with the unit by its actual counit. The finite compact projection formula handles
its additional pulled-back factors and all stated pairs. Finite type over k makes every
coordinate scheme and proper compactification Noetherian of finite dimension.
4. thm-amb-vector-bundle-purity makes the integration transpose P at the unit invertible.
lem-pur-vector-integration-site-comparison identifies this exact map on the two sites.
It gives a bounded constructible origin for omega; projection applies also at (omega,K).
5. Naturality of the inverse canonical projection gives Pi_omega F(1 tensor P) =
(1 tensor F(P)) Pi_L. The transpose equation epsilon F(P)=t identifies the transpose
of theta(1 tensor P) with (1 tensor t)Pi_L. Injectivity of the bounded etale-origin
Hom bijection thm-sf-ambient-adjoint-class proves the equality. Canonical unitors,
symmetries and Tate reassociations are the same ones on both sides.
6. At d=0 use the identity tower adjunction. At zero coefficients and on empty schemes,
all arrows in their displayed domains are the unique zero-object arrows. No reducedness,
ramification divisibility, or nonzero cohomology is used.
-/
theorem affine_coefficient_counit_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Ring P))))
    (_hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y K) :
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    FiniteAffineNormalization (Ring P) P.coefficients.l Y (modulusUnit P Y aY) K := by
  sorry

/-- The ordinary actual counit equals inverse canonical projection followed by
coefficient tensor the actual restricted trace.
Source: affine-line counit equality
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def LineNormalization (A : Type (u + 1)) [CommRing A] [Finite A] (Y : Scheme.{u})
    (W M : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} Y))
    (H : Etale.DerivedCategoryModule A Y)
    (eM : M ≅ AffineLinePurity.ordinarySourceObject A
      (AffineSpace PUnit.{u + 1} Y ↘ Y) W H)
    (epsilon : (Etale.affineTraceLineLeft A Y).obj M ⟶ H)
    (I : (Etale.affineTraceLineLeft A Y).obj W ⟶ Etale.ordinaryFiniteUnit A Y) : Prop :=
  ∃ e : ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).obj
      ((Etale.affineTraceLineLeft A Y).obj W) ≅
      (Etale.affineTraceLineLeft A Y).obj
        (AffineLinePurity.ordinarySourceObject A (AffineSpace PUnit.{u + 1} Y ↘ Y) W H),
  e.hom = lineProjection A Y W H ∧
  epsilon = (Etale.affineTraceLineLeft A Y).map eM.hom ≫ e.inv ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).map I ≫
    (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y H).hom

/-- Ordinary counit normalization together with its exact pro-etale integration and
exceptional transpose. The representative and all canonical source maps are retained.
Source: main-20261015, affine-line normalization
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def LineCompatibility (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Ring P))))
    (H : Etale.DerivedCategoryModule (Ring P) Y)
    (hH : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y H)
    (eH : (comparison (Ring P) Y).obj H ≅ K.obj) : Prop :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  LineNormalization (Ring P) Y
    (AffineLinePurity.etaleCoefficient P.coefficients.l P.extension (P.level - 1) Y r hA)
    (AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1) Y r hA H) H
    (eqToIso (AffineLinePurity.etaleSource_eq P.coefficients.l P.extension
      (P.level - 1) Y r hA H))
    (finiteLineCounit P Y aY r hA H) (finiteLineTrace P Y aY r hA) ∧
  realizeCounit (Ring P) _ (affineTraceLineCompactification Y)
    ⟨AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1) Y r hA H,
      AffineLinePurity.etaleSource_plus P.coefficients.l P.extension (P.level - 1)
        Y r hA H hH⟩
    (AffineLinePurity.source P.coefficients.l P.extension (P.level - 1) Y r hA K.obj)
    H K.obj
    (AffineLinePurity.sourceComparison P.coefficients.l P.extension (P.level - 1)
      Y r hA K.obj H eH) eH (finiteLineCounit P Y aY r hA H) =
      AffineLinePurity.augmentation P.coefficients.l P.extension (P.level - 1)
        Y r hA (AffineLinePurity.primeUnit P Y aY) P.field.k aY K.obj H hH eH ∧
  AffineLinePurity.affineLinePurityComparison P Y r hA aY K H hH eH =
    specifiedExceptionalHomEquiv (Ring P) (affineTraceLineCompactification Y)
      ⟨AffineLinePurity.source P.coefficients.l P.extension (P.level - 1) Y r hA K.obj,
        AffineLinePurity.source_plus P.coefficients.l P.extension (P.level - 1)
          Y r hA K.obj H hH eH⟩
      (AffineLinePurity.sourceWitness P.coefficients.l P.extension (P.level - 1)
        Y r hA K.obj H hH eH) K
      (realizeCounit (Ring P) _ (affineTraceLineCompactification Y)
        ⟨AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1) Y r hA H,
          AffineLinePurity.etaleSource_plus P.coefficients.l P.extension (P.level - 1)
            Y r hA H hH⟩
        (AffineLinePurity.source P.coefficients.l P.extension (P.level - 1) Y r hA K.obj)
        H K.obj
        (AffineLinePurity.sourceComparison P.coefficients.l P.extension (P.level - 1)
          Y r hA K.obj H eH) eH (finiteLineCounit P Y aY r hA H))

/-- The actual affine-line counit and its specified exceptional transpose have the
stated normalized formulas at every positive coefficient level and every annihilator.
Source: main-20261015, projection-purity agreement, affine-line calculation
(blueprint: lem-pur-affine-coefficient-counit-normalization).
Proof: compose the normalized projective-line adjunction with open extension.
Its counit is pushforward of the open counit followed by the projective counit.
Proper projection naturality and the open tensor comparison move that open counit
into the coefficient factor, leaving precisely lineTrace and inverse lineProjection.
The finite compact projection formula proves invertibility on the bounded finite-Tor
domain. The vector integration site comparison identifies the trace, projection,
source comparisons and counits; their pasted square is the augmentation equality.
Apply the specified bounded etale-origin exceptional Hom bijection to this equality.
It identifies the transpose with the recorded integration-defined gamma, including
levels outside the original ramification-divisible range. Root-power transitions
commute with all these maps, proving independence of the annihilating exponent.
At zero input and on the empty scheme the maps are unique zero-object arrows. -/
theorem affine_line_counit_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Ring P))))
    (H : Etale.DerivedCategoryModule (Ring P) Y)
    (hH : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y H)
    (eH : (comparison (Ring P) Y).obj H ≅ K.obj) :
    LineCompatibility P Y aY r hA K H hH eH := by
  sorry

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

set_option maxHeartbeats 800000 in
-- The retained Hom chain contains several derived-functor comparison types.
private theorem specified_source_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).IsLeftAdjoint]
    (M M' : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A M)
    (W' : Scheme.FixedEtaleOriginWitness X A M')
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M.obj ⟶ M'.obj)
    (g : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj M'.obj ⟶ K.obj) :
    specifiedExceptionalHomEquiv A c M W K
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).map e ≫ g) =
      e ≫ specifiedExceptionalHomEquiv A c M' W' K g := by
  let C := VectorIntegrationSite.comparison A X
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  obtain ⟨q, hq⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
    W.complex.obj W'.complex.obj W'.complex.property).2
      (W.iso.hom ≫ e ≫ W'.iso.inv)
  change C.map q = _ at hq
  have hs : C.map q ≫ W'.iso.hom = W.iso.hom ≫ e := by
    rw [hq]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (fixedCompactSupportComparisonIso A c).inv.naturality
    (ObjectProperty.homMk q : W.complex ⟶ W'.complex)
  change (comparison A Y).map
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map q) ≫
      (fixedCompactSupportComparisonIso A c).inv.app W'.complex =
    (fixedCompactSupportComparisonIso A c).inv.app W.complex ≫ F.map (C.map q) at hn
  have he : W.iso.inv ≫ C.map q = e ≫ W'.iso.inv := by
    apply (cancel_epi W.iso.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun z ↦ z ≫ W'.iso.inv) hs
  dsimp only [specifiedExceptionalHomEquiv, Equiv.trans_apply, Iso.homFromEquiv_apply,
    Equiv.ofBijective_apply, Functor.mapIso_symm, Iso.symm_inv]
  change W.iso.inv ≫ C.map
      ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c)).homEquiv _ _
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj
          ((fixedCompactSupportComparisonIso A c).inv.app W.complex ≫
            F.map W.iso.hom ≫ F.map e ≫ g))) =
    e ≫ W'.iso.inv ≫ C.map
      ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c)).homEquiv _ _
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj
          ((fixedCompactSupportComparisonIso A c).inv.app W'.complex ≫
            F.map W'.iso.hom ≫ g)))
  rw [← F.map_comp_assoc, ← hs, F.map_comp_assoc, ← reassoc_of% hn]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    C.map_comp]
  erw [← Category.assoc, he, Category.assoc]
  simp only [Etale.rightDerivedLowerShriekOfCompactification, Functor.comp_obj]

attribute [local irreducible] Adjunction.ofIsLeftAdjoint Adjunction.homEquiv
  Functor.rightAdjoint fixedCompactSupportComparisonIso specifiedExceptionalHomEquiv
  derivedComparisonAdjunction


set_option maxHeartbeats 800000 in
-- Comparing the retained source witnesses elaborates the specified derived Hom chain.
/-- The actual integration augmentation and its specified transpose are independent
of the annihilating exponent, under the canonical normalized Tate source transition.
Source: main-20261015, affine-line normalization, independence paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization).
Proof: choose a common larger annihilating ell-power. The specified root-power
transition commutes with the normalized projective trace by the trace datum and
with open restriction by naturality. The vector integration site comparison carries
these squares and the canonical projection square to the pro-etale site. Tensor
with the pullback of K and use the right unitor to identify the actual augmentations.
Apply naturality of the specified exceptional Hom bijection in its source to obtain
the same equality for their transposes. The normalized Tate comparisons identify
the resulting source transition with lineSourceTransition. This argument uses no
ramification divisibility and includes the zero object and the empty scheme. -/
theorem affine_line_exponent_independence
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Ring P))))
    (H : Etale.DerivedCategoryModule (Ring P) Y)
    (hH : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y H)
    (eH : (comparison (Ring P) Y).obj H ≅ K.obj) (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0) :
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification Y)).map
        (lineSourceTransition P Y aY r r' hA hA' K.obj).hom ≫
      AffineLinePurity.augmentation P.coefficients.l P.extension (P.level - 1)
        Y r' hA' (AffineLinePurity.primeUnit P Y aY) P.field.k aY K.obj H hH eH =
      AffineLinePurity.augmentation P.coefficients.l P.extension (P.level - 1)
        Y r hA (AffineLinePurity.primeUnit P Y aY) P.field.k aY K.obj H hH eH ∧
    (lineSourceTransition P Y aY r r' hA hA' K.obj).hom ≫
      AffineLinePurity.affineLinePurityComparison P Y r' hA' aY K H hH eH =
      AffineLinePurity.affineLinePurityComparison P Y r hA aY K H hH eH := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have hc := (CoordinateLine.coordinateLineAdjunction P Y aY).2.2.2.2.2.2.2.2
    r r' hA hA'
    (primeUnit P (ProjectiveLine Y) ((ProjectiveLine Y ↘ Y) ≫ aY))
    (primeUnit P (AffineSpace PUnit.{u + 1} Y)
      ((AffineSpace PUnit.{u + 1} Y ↘ Y) ≫ aY)) K H hH eH
  have he : (CoordinateLine.sourceExponentIso P Y r hA r' hA'
      (primeUnit P (ProjectiveLine Y) ((ProjectiveLine Y ↘ Y) ≫ aY))
      (primeUnit P (AffineSpace PUnit.{u + 1} Y)
        ((AffineSpace PUnit.{u + 1} Y ↘ Y) ≫ aY)) K.obj).hom =
      (lineSourceTransition P Y aY r r' hA hA' K.obj).hom := by
    unfold CoordinateLine.sourceExponentIso CoordinateLine.tensorCoefficientIso
      lineSourceTransition sourceChange
    rfl
  rw [he] at hc
  refine ⟨?_, hc⟩
  unfold affineLinePurityComparison comparisonFromOrigin at hc
  apply (specifiedExceptionalHomEquiv (Ring P) (affineTraceLineCompactification Y)
    ⟨_, source_plus P.coefficients.l P.extension (P.level - 1) Y r hA K.obj H hH eH⟩
    (sourceWitness P.coefficients.l P.extension (P.level - 1) Y r hA K.obj H hH eH)
    K).injective
  rw [specified_source_naturality (Ring P) (affineTraceLineCompactification Y) _ _ _
    (sourceWitness P.coefficients.l P.extension (P.level - 1) Y r' hA' K.obj H hH eH)]
  exact hc


end AlgebraicGeometry.ProEtale.AffineCoefficientCounit
