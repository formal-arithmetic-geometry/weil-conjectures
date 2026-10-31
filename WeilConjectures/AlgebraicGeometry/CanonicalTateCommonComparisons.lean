/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SixFunctors.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
public import WeilConjectures.AlgebraicGeometry.OrientationIntegralCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.IntegralTwistBaseChange
public import WeilConjectures.AlgebraicGeometry.SignedTwistReductionComparison
public import WeilConjectures.AlgebraicGeometry.CanonicalTateScalarComparisons
import WeilConjectures.AlgebraicGeometry.PrincipalKoszulStrictReplacement

/-! # Canonical Tate comparisons at a common coefficient stage

Source: current blueprint, def-pur-tate-datum, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-common-comparisons).
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

attribute [-instance] PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  IntegralOnSlice.duality IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory IntegralOnSlice.tower
  IntegralOnSlice.augmentation integralOperationsTensorTowerFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] rationalPull rationalProduct rationalDerivedPullback

/-- The common-stage pullback line map keeps the specified least finite stage.
Source: blueprint common-stage construction of the Tate datum
(blueprint: def-pur-canonical-tate-common-comparisons). -/
def commonPull (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (r : ℕ) :
    (commonStageDerivedPullback l Ω f).obj (sfQbarTwistingCoefficient l Y Ω (r : ℤ)) ≅
      sfQbarTwistingCoefficient l X Ω (r : ℤ) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
      (sfQbarTwistingCoefficient l Y Ω (r : ℤ))) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (Padic.finiteCoefficientBase l Ω)).mapIso
        (rationalPull l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω)) f r)

attribute [local irreducible] commonPull commonStageDerivedPullback

/-- The chosen common-stage line evaluated at an arbitrary larger coefficient field.
Source: blueprint common-stage transition and integral base change
(blueprint: def-pur-canonical-tate-common-comparisons). -/
def commonLineAtStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (r : ℕ) (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (sfQbarTwistingCoefficient l X Ω (r : ℤ)).stage ≤ L) :
    (sfQbarTwistingCoefficient l X Ω (r : ℤ)).toStage h ≅
      sfRationalTwistingCoefficient l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (r : ℤ) :=
  (operationStageTransitionIso l Ω X _ L h).app
      (sfQbarTwistingCoefficient l X Ω (r : ℤ)).obj ≪≫
    rationalScalarLine l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω))
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω _ L h) X r

/-- The common-stage tensor-power map, specified at every common larger stage.
Source: blueprint common-stage tensor and root-line products
(blueprint: def-pur-canonical-tate-common-comparisons).
Proof: represent both lines and their product at one finite compositum. The tensor
transition comparison, the two scalar-normalized line comparisons and the rational
product give the displayed map. It is invertible because each factor is. The scalar
unit and tensor associativity identities give the same class after every enlargement.
Every common-stage arrow has a representative, proving uniqueness. -/
theorem commonProduct_existsUnique (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (r s : ℕ) :
    ∃! e : (commonStageDerivedTensor l Ω X).obj
        (sfQbarTwistingCoefficient l X Ω (r : ℤ),
          sfQbarTwistingCoefficient l X Ω (s : ℤ)) ≅
      sfQbarTwistingCoefficient l X Ω ((r + s : ℕ) : ℤ),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω X
          (sfQbarTwistingCoefficient l X Ω (r : ℤ))
          (sfQbarTwistingCoefficient l X Ω (s : ℤ))).stage ≤ L)
        (h' : (sfQbarTwistingCoefficient l X Ω ((r + s : ℕ) : ℤ)).stage ≤ L),
        HEq e.hom (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStageTensorObject l Ω X (sfQbarTwistingCoefficient l X Ω (r : ℤ))
            (sfQbarTwistingCoefficient l X Ω (s : ℤ)))
          (sfQbarTwistingCoefficient l X Ω ((r + s : ℕ) : ℤ)) L h h'
          ((commonStageTensorComparison l Ω X
            (sfQbarTwistingCoefficient l X Ω (r : ℤ))
            (sfQbarTwistingCoefficient l X Ω (s : ℤ)) L h).hom ≫
          (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            X).map (Prod.mkHom
              (commonLineAtStage l Ω X r L
                (((Padic.finiteCoefficientFields_properties l Ω).1 _ _).1.trans h)).hom
              (commonLineAtStage l Ω X s L
                (((Padic.finiteCoefficientFields_properties l Ω).1 _ _).2.trans h)).hom) ≫
          (rationalProduct l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            X r s).hom ≫ (commonLineAtStage l Ω X (r + s) L h').inv)) := by
  sorry

/-- The common-stage product determined by the full representative normalization.
Source: blueprint common-stage Tate products
(blueprint: def-pur-canonical-tate-common-comparisons). -/
def commonProduct (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (r s : ℕ) :=
  (commonProduct_existsUnique l Ω X r s).exists.choose

/-- Pullback commutation in the common-stage category, with its actual compositors.
Source: blueprint common-stage pullback comparison
(blueprint: def-pur-canonical-tate-common-comparisons). -/
def commonSquare (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω w).obj ((commonStageDerivedPullback l Ω g).obj M) ≅
      (commonStageDerivedPullback l Ω g').obj ((commonStageDerivedPullback l Ω w).obj M) :=
  (pullbackTensorCommonComposition l Ω g w M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj M) h.symm) ≪≫
    pullbackTensorCommonComposition l Ω w g' M

end WeilConjectures.CanonicalTate
