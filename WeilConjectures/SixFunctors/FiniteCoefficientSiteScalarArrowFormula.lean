/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow

/-! # The specified finite scalar/site comparison, on components

Source: blueprint thm-coef-finite-hom, final site-comparison sentence;
Stacks 00YV and 03CY (blueprint: def-sf-finite-coefficient-site-scalar-arrow).
The imported definitions construct the ordinary inverse image and normalized
restriction isomorphism directly. This module records the explicit component
formula for their derived scalar adjunction mate. No map is chosen by this theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The inverse mate is the prescribed unit--inverse-restriction--counit composite.
Source: blueprint thm-coef-finite-hom, final site-comparison sentence; Stacks 00YV
(blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: unfold finiteHomSiteBeta and Mathlib's mateEquiv inverse. Evaluate its
whiskered transformations at T. Functoriality sends the associator identities to
identities; cancel these and the two unitors. The remaining three factors are,
in order, pro-etale scalar extension applied to the inverse image of the etale
unit, pro-etale scalar extension applied to rho inverse at the extended object,
and the pro-etale counit. This works also for the identity quotient n=m. -/
theorem finiteHomSiteBeta_app {n m : ℕ} (h : m ≤ n) (T : finiteHomEtale l E X n) :
    (finiteHomSiteBeta l E X h).app T =
      (coefficientFiniteQuotientDerived l E X h).map
        ((finiteHomNu l E X n).map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (finiteHomQuotient l E h))).unit.app T)) ≫
      (coefficientFiniteQuotientDerived l E X h).map
        ((finiteHomNuDerivedRestriction l E X h).inv.app
          ((finiteHomEtaleReduction l E X h).obj T)) ≫
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
        h).counit.app ((finiteHomNu l E X m).obj
          ((finiteHomEtaleReduction l E X h).obj T)) := by
  sorry

end WeilConjectures
