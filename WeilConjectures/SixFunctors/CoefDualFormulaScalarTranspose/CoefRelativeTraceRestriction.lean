/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaFiniteTrace
public import WeilConjectures.SixFunctors.Compact.CompactSupportNormalizedRealization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange

/-! # Restriction maps used in the finite relative trace square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

/-- The intrinsic proper/open restriction comparison in normalized quotient coordinates.
Source: the compact-support coefficient restriction construction
(blueprint: def-coef-relative-trace-restriction). -/
def finiteSupportRestriction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E X h ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (m + 1)) c ≅
      sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c ⋙
        normalizedDVRRes l E Y h :=
  Functor.isoWhiskerRight (coefCompactSupportRestrictionIso l E X h) _ ≪≫
    sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h) ≪≫
    Functor.isoWhiskerLeft _ (coefCompactSupportRestrictionIso l E Y h).symm

/-- The etale proper/open restriction comparison, retained in the ambient categories
on its bounded-below source. Source: compact-support restriction on D+
(blueprint: def-coef-relative-trace-restriction). -/
def finiteEtaleSupportRestriction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K.obj) ⟶
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
          K.obj) :=
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusCompatibility.inv.app
        K) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).inv.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K) ≫
    DerivedCategory.Plus.ι.map ((Etale.compactSupportCoefficientRestrictionPlus φ c).hom.app K) ≫
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusCompatibility.hom.app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c).obj K) ≫
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} B) c).hom.app K)

/-- The site and intrinsic coefficient comparison on every bounded-below etale input.
Source: the canonical compact-support site comparison
(blueprint: def-coef-relative-trace-restriction). -/
def finiteSupportRealization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    DerivedCategory.Plus.ι ⋙ finiteDualizingRealization l E X n ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c ⋙
        finiteDualizingRealization l E Y n :=
  Functor.isoWhiskerLeft
      (DerivedCategory.Plus.ι ⋙ (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).mapDerivedCategory)
      (ProEtale.sfIntrinsicCompactSupportComparison
        (Padic.coefficientExtensionRing l E (n + 1)) c) ≪≫
    Functor.isoWhiskerRight (ProEtale.compactSupportSiteComparison
      (finiteDualizingCoeff l E n) c)
      (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor

end WeilConjectures.CoefDualFormulaScalarTranspose
