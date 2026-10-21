/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Indices n and m below denote exponents n + 1 and m + 1; thus every positive
exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The actual comparison on module sheaves, with finite coefficients supplied.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuOrdinary (n : ℕ) :
    Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) ⥤
      normalizedDVRModules l E X n :=
  @ProEtale.finiteCoefficientIntrinsicComparison X (Padic.coefficientExtensionRing l E (n + 1))
    inferInstance

/-- Additivity of the published intrinsic comparison, at the positive finite stage.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
instance finiteHomNuOrdinary_additive (n : ℕ) : (finiteHomNuOrdinary l E X n).Additive :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  inferInstanceAs (ProEtale.finiteCoefficientIntrinsicComparison X
    (Padic.coefficientExtensionRing l E (n + 1))).Additive

/-- Exact comparison preserves finite limits.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
instance finiteHomNuOrdinary_limits (n : ℕ) :
    PreservesFiniteLimits (finiteHomNuOrdinary l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  inferInstanceAs (PreservesFiniteLimits (ProEtale.finiteCoefficientIntrinsicComparison X
    (Padic.coefficientExtensionRing l E (n + 1))))

/-- Exact comparison preserves finite colimits.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
instance finiteHomNuOrdinary_colimits (n : ℕ) :
    PreservesFiniteColimits (finiteHomNuOrdinary l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  inferInstanceAs (PreservesFiniteColimits (ProEtale.finiteCoefficientIntrinsicComparison X
    (Padic.coefficientExtensionRing l E (n + 1))))

/-- The exact derived inverse image nu_X^* in the intrinsic constant-ring presentation.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNu (n : ℕ) : finiteHomEtale l E X n ⥤ normalizedDVRDerived l E X n :=
  (finiteHomNuOrdinary l E X n).mapDerivedCategory

/-- A section mapped by the comparison unit and the associated-module-sheaf unit.
Source: blueprint site formula; Stacks 00YV
(blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuSection (n : ℕ)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)) :
    ((finiteHomNuOrdinary l E X n).obj M).val.obj (op (X.toProEt.obj U)) :=
  (((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap X
        (Padic.coefficientExtensionRing l E (n + 1)))).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).obj M).obj)).app
      (op (X.toProEt.obj U)))
    ((((ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).unit.app M).hom.app
        (op U)) x)

/-- Identity-on-generators normalization for comparison and scalar restriction.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def FiniteHomNuRestrictionNormalization {n m : ℕ} (h : m ≤ n)
    (σ : finiteHomNuOrdinary l E X m ⋙ normalizedDVRModuleRes l E X h ≅
      Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNuOrdinary l E X n) : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)),
    ∃ (z : ((finiteHomNuOrdinary l E X m ⋙
          normalizedDVRModuleRes l E X h).obj M).val.obj (op (X.toProEt.obj U)))
      (y : ((Sheaf.restrictScalars X.smallEtaleTopology
          (finiteHomQuotient l E h)).obj M).obj.obj (op U)),
      HEq z (finiteHomNuSection l E X m M U x) ∧ HEq y x ∧
      HEq (((σ.hom.app M).val.app (op (X.toProEt.obj U))) z)
        (finiteHomNuSection l E X n
          ((Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)).obj M) U y)

/-- Restriction commutes canonically with inverse image, fixing every local generator.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: on underlying module presheaves scalar restriction does not change sections.
The two inverse-image constructions are left Kan extension followed by module
sheafification. The identity on the displayed generators respects scalar balancing,
restriction, and gluing. It extends to a natural isomorphism; the identity in the
opposite direction is inverse. These generators locally generate the associated
sheaf, so the normalization determines every component uniquely. -/
theorem finiteHomNuRestriction_existsUnique {n m : ℕ} (h : m ≤ n) :
    ∃! σ, FiniteHomNuRestrictionNormalization l E X h σ := by
  sorry

/-- The uniquely normalized ordinary scalar-restriction comparison.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuRestriction {n m : ℕ} (h : m ≤ n) :
    finiteHomNuOrdinary l E X m ⋙ normalizedDVRModuleRes l E X h ≅
      Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNuOrdinary l E X n :=
  (finiteHomNuRestriction_existsUnique l E X h).choose

/-- Exact descent of the canonical scalar-restriction comparison.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuDerivedRestriction {n m : ℕ} (h : m ≤ n) :
    finiteHomNu l E X m ⋙ normalizedDVRRes l E X h ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNu l E X n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteHomNuRestriction l E X h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Beta is the canonical left-adjoint mate of identity-on-sections scalar restriction.
Source: blueprint nu_X^* coefficient formula
(blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomSiteBeta {n m : ℕ} (h : m ≤ n) :
    finiteHomNu l E X n ⋙ coefficientFiniteQuotientDerived l E X h ⟶
      finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)))
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)).symm
    (TwoSquare.mk _ _ _ _ (finiteHomNuDerivedRestriction l E X h).inv)).natTrans

/-- The specified beta mate is invertible on every ambient object.
Source: blueprint site-comparison paragraph
(blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: compute both scalar extensions on flat K-flat resolutions. Exact inverse
image preserves them. The mate sends each local balanced tensor to that same
tensor, by finiteHomNuRestrictionNormalization. The opposite pure-tensor map is
its inverse. Localization proves invertibility without quotient flatness. -/
@[instance] theorem finiteHomSiteBeta_isIso {n m : ℕ} (h : m ≤ n) :
    IsIso (finiteHomSiteBeta l E X h) := by
  sorry


end WeilConjectures
