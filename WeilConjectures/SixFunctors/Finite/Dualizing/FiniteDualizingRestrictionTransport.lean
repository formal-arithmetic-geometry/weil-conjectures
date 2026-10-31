/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingRestrictionTransportCore

/-! # Transport of finite-coefficient restriction coherence -/

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

/-- Transport of the intrinsic restriction coherence across comparison.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
comparison-site pasting and naturality part of the restriction composition proof
(blueprint: lem-coef-dualizing-realization-restriction-transport).

Proof: the comparison restriction inverse for the composite is the pasted
pair of successive comparison inverses, by conjugating the ordinary
restriction square and applying exact derived localization. Naturality of the
intrinsic restriction isomorphism moves the middle comparison map through the
square; functoriality of normalized restriction then maps the final component.
Evaluating this pasted diagram at K gives exactly the displayed equality. -/
theorem finiteDualizingRealizationRestriction_transport
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
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K)) ≫
      (normalizedDVRRes l E X hrm).map
        ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app
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
            (finiteDualizingQuotient l E hmn)).inv.app K)) ≫
      (normalizedDVRRes l E X hrm).map
        ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K)) := by
  let Cn := ProEtale.comparisonUpperStar
    (ModuleCat (finiteDualizingCoeff l E n)) X
  let CK := Cn.mapDerivedCategory.obj K
  have hcore := finiteDualizingRealizationRestriction_transport_core
    l E X hrm hmn K
  have hpost := congrArg (fun f ↦
      f ≫ (normalizedDVRRes l E X hrm).map
        ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app CK)) hcore
  simpa only [Category.assoc] using hpost

end WeilConjectures
