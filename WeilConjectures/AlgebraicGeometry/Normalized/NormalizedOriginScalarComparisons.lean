/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.PbcFixedScalarExtension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement

/-!
# Canonical unit and reassociation for quotient scalar extensions

Source: Stacks Tags 06YY and 09B1, coefficient refinement of the compatible-origin argument
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons).
The definitions are relocated verbatim from NormalizedEtaleOriginWitnesses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Canonical identity restriction on sheaves, given by identity section maps.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginRestrictionUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    Sheaf.restrictScalars J φ ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' φ hφ) ≪≫
        F.obj.rightUnitor))
    (fun {F G} f ↦ by
      apply (fullyFaithfulSheafToPresheaf J _).map_injective
      ext U x
      rfl)

/-- Canonical self-extension unit, the adjunction mate of identity scalar restriction.
It is the derived map x tensor a to ax, not a chosen automorphism.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginScalarUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) :
    pbcFixedScalarExtension J φ ≅ 𝟭 (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  Adjunction.leftAdjointIdIso (Adjunction.ofIsRightAdjoint _)
    (Functor.mapDerivedCategoryNatIso (normalizedOriginRestrictionUnit J φ hφ) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- The actual map `A_{E,m} → A_{E,n}`, induced by the identity on the valuation ring.
The exponent is positive, with `n = 1` the first finite quotient.
Source: blueprint `prop-coef-integral-dualizing`, proof, reductions
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientMap (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m n : ℕ+) (h : n ≤ m) :
    Padic.coefficientExtensionRing l E m →+* Padic.coefficientExtensionRing l E n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right h)

/-- The normalized identity unit on the actual positive finite coefficient quotient.
Source: blueprint `prop-coef-integral-dualizing`, proof, scalar adjunction
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ+) :
    pbcFixedScalarExtension J (normalizedOriginQuotientMap l E n n (le_refl n)) ≅ 𝟭 _ :=
  normalizedOriginScalarUnit J _ Ideal.Quotient.factor_eq

/-- The normalized compositor for three actual positive quotient levels, including ties.
Source: blueprint `prop-coef-integral-dualizing`, proof, successive reductions
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientComp
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k m n : ℕ+) (hnm : n ≤ m) (hmk : m ≤ k) :
    pbcFixedScalarExtension J (normalizedOriginQuotientMap l E k m hmk) ⋙
        pbcFixedScalarExtension J (normalizedOriginQuotientMap l E m n hnm) ≅
      pbcFixedScalarExtension J (normalizedOriginQuotientMap l E k n (hnm.trans hmk)) :=
  pbcFixedScalarExtensionComp J _ _ _
    (Ideal.Quotient.factor_comp (Ideal.pow_le_pow_right hmk)
      (Ideal.pow_le_pow_right hnm)).symm

/-- Scalar extension along the actual quotient map on any essentially small site.
In particular, substituting the small etale or pro-etale topology gives both site instances.
Source: blueprint `prop-coef-integral-dualizing`, proof, reductions and scalar adjunction
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
abbrev normalizedOriginReduction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m n : ℕ+) (h : n ≤ m) :=
  pbcFixedScalarExtension J (normalizedOriginQuotientMap l E m n h)

end AlgebraicGeometry.ProEtale
