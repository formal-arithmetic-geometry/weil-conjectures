/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! # Comparison-site transport core for finite dualizing restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

/--
The comparison-site part of the finite dualizing restriction transport.

Source: current blueprint, `lem-coef-finite-dualizing.proof.md`, final sentence;
this is the comparison pasting subdiagram before the final normalized restriction
component is appended.  The proof is the ordinary comparison restriction square
for the composite quotient, transported through exact derived localization and
then through the intrinsic restriction comparison.  The corresponding derived
square is obtained by the standard `mapDerivedCategorySquareIso` composition
lemma; naturality of the intrinsic restriction comparison gives the displayed
middle component.  This core is strictly simpler than the full transport because
it omits the final normalized restriction map, which is appended functorially in
the proof of the main theorem.
(blueprint: new-finitedualizing-restriction-transport-core)
-/
theorem finiteDualizingRealizationRestriction_transport_core
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X) :
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E (hmn.trans hrm))).inv.app K) ≫
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K)) ≫
      (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology X)
          (finiteDualizingQuotient l E hmn)).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K)) =
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat (finiteDualizingCoeff l E r)) X).mapDerivedCategory.map
          ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
            (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K)) ≫
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E hrm)).inv.app
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
            (finiteDualizingQuotient l E hmn)).obj K)) ≫
      (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat (finiteDualizingCoeff l E m)) X).mapDerivedCategory.obj
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
            (finiteDualizingQuotient l E hmn)).obj K)) ≫
      (normalizedDVRRes l E X hrm).map
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).functor.map
          ((ProEtale.pbcDerivedComparisonRestrict X
            (finiteDualizingQuotient l E hmn)).inv.app K)) := by
  sorry

end WeilConjectures
