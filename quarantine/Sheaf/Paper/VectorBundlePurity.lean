/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityBaseChange
public import Sheaf.Paper.VectorPurityDirectSum
public import Sheaf.Paper.VectorPurityFiniteReduction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.CompactProjectionExchange
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import Sheaf.AlgebraicGeometry.ShriekTensorComposition
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
import Sheaf.Paper.DegreeZeroDerivedMapGluing
import Sheaf.Paper.EtaleCompactScalarCoherence
import Sheaf.Paper.PurityFiniteSetting
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.VectorPurityNormalization
import Sheaf.Paper.VectorPurityScalarSingle
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import Sheaf.Targets.VectorBundlePurity

/-! # Vector-bundle purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: cor-pur-vector-bundle-purity).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The finite purity convention, realized on the ordinary derived category.
All geometric and characteristic witnesses follow from the fixed setting.
Source: purity conventions and vector-bundle purity
(blueprint: cor-pur-vector-bundle-purity). -/
def VectorBundlePurityConclusion (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType hB] [QuasiCompact hB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType hB
  letI : IsAffineHom (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).2.1
  ∃ hN : IsUnit (ringChar P.Coefficient : Γ(B, ⊤)),
    VectorPurityFunctorConclusion P.Coefficient (VectorBundleZeroSection.π B d F)
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) B)
      (P.vectorPurityEtaleCoefficient B d F) (P.vectorPurityTrace B d F hN) ∧
    ∃ γ : VectorPurityGamma P.Coefficient (ringChar P.Coefficient)
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B d F,
    VectorPurityGammaNormalized P.Coefficient (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ ∧
    (∀ K : (Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) B).FullSubcategory, IsIso (γ.app K.obj)) ∧
    PurityBaseChangeEquation P.Coefficient (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ ∧
    PurityDirectSumEquation P.Coefficient (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ ∧
    PurityFiniteReductionEquation P (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ

/-- Vector-bundle purity with integration-and-adjunction normalization.
Source: main-20261015 sec-smooth-purity/sk-prop-an, vector-bundle proposition
(blueprint: cor-pur-vector-bundle-purity).

Proof: use the affine finite-type bundle geometry to apply global Nagata
compactification. Ordinary exact extension by zero followed by proper derived direct
image defines Rpi_!. Brown representability on the whole Grothendieck derived
category supplies its right adjoint. Use K-flat resolutions to form tensor and the
projection arrow. The glued, Kummer-normalized integration has invertible adjoint
mate on bounded constructible complexes of finite Tor amplitude. Invert this mate.
The adjunction Hom bijection proves uniqueness and naturality, including its unit
component. Base change preserves the chartwise affine-space trace; equality is glued
as a map of degree-zero sheaves, then transposed. The same argument with iterated
coordinate traces gives direct sums. Scalar extension preserves the Kummer class
and trace, so uniqueness of adjoints and their counit equations gives finite
reduction compatibility. The scalar mate is transposed only after the canonical
compact-support comparison
is inverted. Its source comparison is built from the normalized pure-root tensor
map, the K-flat scalar tensorator and geometric pullback comparison. This gives the
same reduction equality at the coefficient-unit object. The coefficient range is
finite A = A_{E,n}, exactly as specified by the final scope paragraph of the current
def-pur-conventions; the derived-complete, rational and common-stage transports are
separate results of the blueprint's transport section. -/
theorem vectorBundlePurity (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType hB] [QuasiCompact hB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    VectorBundlePurityConclusion P B hB d F := by
  sorry


end WeilConjectures.PurityFiniteSetting
