/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.CanonicalTateComparisons
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
public import Sheaf.Paper.CartesianCoefficientTwists
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.OrientationIntegralCoefficientTwists
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Paper.SignedTwistReductionComparison

/-! # Canonical Tate naturality: NaturalityLaws

Source: current blueprint, def-pur-tate-datum, canonical root-arrow comparisons.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-canonical-tate-naturality-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] HasDerivedCategory.standard
  integralPull finitePull rationalPull commonPull
  integralProduct finiteProduct rationalProduct commonProduct
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The equation of Weil arrows across a specified canonical comparison square.
Source: blueprint displayed pullback and coefficient naturality equations
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def ArrowSquare {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    (G : C ⥤ C) (G' : D ⥤ D) (R : C ⥤ D) (T : C) (T' : D)
    (tau : G.obj T ≅ T) (tau' : G'.obj T' ≅ T')
    (t : R.obj T ≅ T') (comparison : R.obj (G.obj T) ≅ G'.obj (R.obj T)) : Prop :=
  R.map tau.hom ≫ t.hom = comparison.hom ≫ G'.map t.hom ≫ tau'.hom

/-- Tensor additivity for the specified tensor functor and canonical pullback comparison.
Source: blueprint displayed additivity equation
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def Additivity {C : Type a} [Category.{b} C] (G : C ⥤ C) (tensor : C × C ⥤ C)
    (T : ℕ → C) (tau : ∀ r, G.obj (T r) ≅ T r)
    (alpha : ∀ r s, tensor.obj (T r, T s) ≅ T (r + s))
    (mu : ∀ M N, G.obj (tensor.obj (M, N)) ≅ tensor.obj (G.obj M, G.obj N)) : Prop :=
  ∀ r s, (mu (T r) (T s)).hom ≫ tensor.map
    (Prod.mkHom (tau r).hom (tau s).hom) ≫ (alpha r s).hom =
    G.map (alpha r s).hom ≫ (tau (r + s)).hom

/-- The mixed equation on the target of spatial pullback, with the inverse square inserted.
Source: blueprint displayed mixed identity on T'
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def MixedIdentity {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    (G : C ⥤ C) (G' : D ⥤ D) (W : C ⥤ D) (tensor : D × D ⥤ D)
    (T : ℕ → C) (T' : ℕ → D) (tau : ∀ r, G.obj (T r) ≅ T r)
    (tau' : ∀ r, G'.obj (T' r) ≅ T' r) (t : ∀ r, W.obj (T r) ≅ T' r)
    (comparison : ∀ r, W.obj (G.obj (T r)) ≅ G'.obj (W.obj (T r)))
    (alpha : ∀ r s, tensor.obj (T' r, T' s) ≅ T' (r + s))
    (mu : ∀ M N, G'.obj (tensor.obj (M, N)) ≅ tensor.obj (G'.obj M, G'.obj N)) : Prop :=
  ∀ r s, (mu (T' r) (W.obj (T s))).hom ≫
    tensor.map (Prod.mkHom (tau' r).hom
      ((comparison s).inv ≫ W.map (tau s).hom)) ≫
    tensor.map (Prod.mkHom (𝟙 (T' r)) (t s).hom) ≫ (alpha r s).hom =
    G'.map (tensor.map (Prod.mkHom (𝟙 (T' r)) (t s).hom) ≫ (alpha r s).hom) ≫
      (tau' (r + s)).hom

/-- The three geometric equations with their named canonical input maps.
Source: blueprint spatial, additive and mixed identities
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def GeometricLaws {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    (G : C ⥤ C) (G' : D ⥤ D) (W : C ⥤ D) (tensor : D × D ⥤ D)
    (T : ℕ → C) (T' : ℕ → D) (tau : ∀ r, G.obj (T r) ≅ T r)
    (tau' : ∀ r, G'.obj (T' r) ≅ T' r) (t : ∀ r, W.obj (T r) ≅ T' r)
    (comparison : ∀ r, W.obj (G.obj (T r)) ≅ G'.obj (W.obj (T r)))
    (alpha : ∀ r s, tensor.obj (T' r, T' s) ≅ T' (r + s))
    (mu : ∀ M N, G'.obj (tensor.obj (M, N)) ≅ tensor.obj (G'.obj M, G'.obj N)) : Prop :=
  (∀ r, ArrowSquare G G' W (T r) (T' r) (tau r) (tau' r) (t r) (comparison r)) ∧
    Additivity G' tensor T' tau' alpha mu ∧
    MixedIdentity G G' W tensor T T' tau tau' t comparison alpha mu

/-- The three geometric laws at the finite coefficient stage.
Source: blueprint canonical Tate equations at this coefficient stage
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def finiteGeometricLaws {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [IsIso g] [IsIso g'] [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) (n : ℕ) : Prop :=
  GeometricLaws (finiteDerivedPullback l E n g) (finiteDerivedPullback l E n g')
    (finiteDerivedPullback l E n w)
    (finiteIntrinsicDerivedTensor l E X n)
    (fun r ↦ DerivedCategory.Q.obj (finiteComplex l E Y n r)) (fun r ↦ DerivedCategory.Q.obj
      (finiteComplex l E X n r))
    (fun r ↦ finiteTau l E g n r) (fun r ↦ finiteTau l E g' n r)
    (finitePull l E w n ·)
    (fun r ↦ (finiteSquare l E w g g' h n).app (DerivedCategory.Q.obj (finiteComplex l E Y n r)))
    (finiteProduct l E X n)
    (canonicalFinitePullbackTensor l E g' n)

/-- The three geometric laws at the integral coefficient stage.
Source: blueprint canonical Tate equations at this coefficient stage
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def integralGeometricLaws {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [IsIso g] [IsIso g'] [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) : Prop :=
  GeometricLaws (constructibleIntegralPullback l E g) (constructibleIntegralPullback l E g')
    (constructibleIntegralPullback l E w)
    (constructibleIntegralTensor l E X)
    (fun r ↦ sfIntegralTwistingCoefficient l E Y (r : ℤ)) (fun r ↦ sfIntegralTwistingCoefficient
      l E X (r : ℤ))
    (fun r ↦ integralTau l E g r) (fun r ↦ integralTau l E g' r)
    (fun r ↦ ObjectProperty.isoMk _ (integralPull l E w r))
    (fun r ↦ (integralSquare l E w g g' h).app (sfIntegralTwistingCoefficient l E Y (r : ℤ)))
    (fun r s ↦ ObjectProperty.isoMk _ (integralProduct l E X r s))
    (canonicalIntegralPullbackTensor l E g')

/-- The three geometric laws at the rational coefficient stage.
Source: blueprint canonical Tate equations at this coefficient stage
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def rationalGeometricLaws {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [IsIso g] [IsIso g'] [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) : Prop :=
  GeometricLaws (rationalDerivedPullback l E g) (rationalDerivedPullback l E g')
    (rationalDerivedPullback l E w)
    (rationalDerivedTensor l E X)
    (fun r ↦ sfRationalTwistingCoefficient l E Y (r : ℤ)) (fun r ↦ sfRationalTwistingCoefficient
      l E X (r : ℤ))
    (fun r ↦ rationalDerivedLineMap l E g (r : ℤ)) (fun r ↦ rationalDerivedLineMap l E g' (r : ℤ))
    (rationalPull l E w ·)
    (fun r ↦ (rationalSquare l E w g g' h) (sfRationalTwistingCoefficient l E Y (r : ℤ)))
    (rationalProduct l E X)
    (canonicalRationalPullbackTensor l E g')

/-- The three geometric laws at the common coefficient stage.
Source: blueprint canonical Tate equations at this coefficient stage
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def commonGeometricLaws (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [IsIso g] [IsIso g'] [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) : Prop :=
  GeometricLaws (commonStageDerivedPullback l Ω g) (commonStageDerivedPullback l Ω g')
    (commonStageDerivedPullback l Ω w)
    (commonStageDerivedTensor l Ω X)
    (fun r ↦ sfQbarTwistingCoefficient l Y Ω (r : ℤ)) (fun r ↦ sfQbarTwistingCoefficient l X Ω (r
      : ℤ))
    (fun r ↦ commonDerivedLineMap l Ω g (r : ℤ)) (fun r ↦ commonDerivedLineMap l Ω g' (r : ℤ))
    (commonPull l Ω w ·)
    (fun r ↦ (commonSquare l Ω w g g' h) (sfQbarTwistingCoefficient l Y Ω (r : ℤ)))
    (commonProduct l Ω X)
    (canonicalCommonStagePullbackTensor l Ω g')

/-- Coefficient naturality at every quotient and every finite field extension.
Source: blueprint coefficient functor equation and its field images
(blueprint: def-pur-canonical-tate-naturality-laws). -/
def coefficientLaws (X : Scheme.{u}) (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] : Prop :=
  (∀ (m n : ℕ) (h : n ≤ m) (r : ℕ),
    ArrowSquare (finiteDerivedPullback l E m g) (finiteDerivedPullback l E n g)
      (coefficientFiniteQuotientDerived l E X h)
      (DerivedCategory.Q.obj (finiteComplex l E X m r))
      (DerivedCategory.Q.obj (finiteComplex l E X n r))
      (finiteTau l E g m r) (finiteTau l E g n r) (finiteScalarLine l E X h r)
      ((pullbackTensorQuotient l E g h).app
        (DerivedCategory.Q.obj (finiteComplex l E X m r)))) ∧
  (∀ n r : ℕ,
    ArrowSquare (constructibleIntegralPullback l E g) (finiteDerivedPullback l E n g)
      (constructibleReduction l E X n) (sfIntegralTwistingCoefficient l E X (r : ℤ))
      (DerivedCategory.Q.obj (finiteComplex l E X n r))
      (integralTau l E g r) (finiteTau l E g n r) (integralReductionLine l E X n r)
      (reductionSquare l E g n r)) ∧
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (r : ℕ),
    ArrowSquare (constructibleIntegralPullback l E g) (constructibleIntegralPullback l L g)
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X)
      (sfIntegralTwistingCoefficient l E X (r : ℤ))
      (sfIntegralTwistingCoefficient l L X (r : ℤ))
      (integralTau l E g r) (integralTau l L g r) (integralScalarLine l E L ι X r)
      (integralPullbackScalarComparison l E L ι g
        (sfIntegralTwistingCoefficient l E X (r : ℤ))) ∧
    ArrowSquare (rationalDerivedPullback l E g) (rationalDerivedPullback l L g)
      (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
      (sfRationalTwistingCoefficient l E X (r : ℤ))
      (sfRationalTwistingCoefficient l L X (r : ℤ))
      (rationalDerivedLineMap l E g (r : ℤ)) (rationalDerivedLineMap l L g (r : ℤ))
      (rationalScalarLine l E L ι X r)
      ((rationalPullbackScalarComparison l E L ι g).app
        (sfRationalTwistingCoefficient l E X (r : ℤ)))


end WeilConjectures.CanonicalTate
