/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction

/-! # Quotient compatibility of compact-support realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The specified compact-support realization commutes with quotient restriction.
Source: canonical intrinsic and comparison-site proper/open mates, Stacks 09AF,
099R and 0GL6 (blueprint: lem-coef-support-realization-restriction).
Proof: on coefficient sheaves the intrinsic realization comparison is the unique
map preserving scalar-unit sections. This identifies its restriction square with
the identity scalar-action square. On the open factor transpose under extension
by zero: both paths are the comparison inverse-image unit, so the square commutes.
On the proper factor paste the site inverse-image square with coefficient
restriction and take the direct-image counit mate. Right derivation preserves
that mate equation. Whisker the two factor squares and pass through the canonical
D+ inclusions. Their compatibility maps are exactly the factors defining
finiteEtaleSupportRestriction and finiteSupportRealization. The sectionwise
normalization identifies the quotient restriction with normalizedDVRRes and
finiteDualizingRealizationRestriction, giving precisely the displayed square. -/
theorem finiteSupportRealization_restriction {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) :
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (m + 1)) c).map
        ((finiteDualizingRealizationRestriction l E X h).hom.app K.obj) ≫
      (finiteSupportRealization l E c m).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology
          (finiteDualizingQuotient l E h)).mapDerivedCategoryPlus.obj K) ≫
      (finiteDualizingRealization l E Y m).map
        (finiteEtaleSupportRestriction (finiteDualizingQuotient l E h) c K) =
    (finiteSupportRestriction l E c h).hom.app
        ((finiteDualizingRealization l E X n).obj K.obj) ≫
      (normalizedDVRRes l E Y h).map ((finiteSupportRealization l E c n).hom.app K) ≫
      (finiteDualizingRealizationRestriction l E Y h).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj K.obj) := by
  sorry

end WeilConjectures.CoefDualFormulaScalarTranspose
