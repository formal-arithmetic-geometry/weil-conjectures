/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionCompLhs

/-! Natural-transformation form of intrinsic finite-dualizing restriction composition. -/
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

/-- The Qh comparison extends by localization to a natural-transformation identity.
Source: the localization extension step in the intrinsic restriction composition proof
(blueprint: lem-coef-dualizing-intrinsic-restriction-comp-nattrans-x7).

The Qh case is the section-level pasting calculation. Exact localization and
naturality extend it to all derived objects. -/
theorem finiteDualizingIntrinsicRestriction_comp_natTrans_exists
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    ∃ rhs :
        (Sheaf.derivedRestrictScalars (ProEt.topology X)
            (finiteDualizingQuotient l E (hmn.trans hrm)) ⋙
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (r + 1))).functor) ⟶
        (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
          normalizedDVRRes l E X hmn ⋙ normalizedDVRRes l E X hrm,
      finiteDualizingIntrinsicRestrictionCompLhs l E X hrm hmn = rhs ∧
      ∀ K, rhs.app K =
        (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (r + 1))).functor.map
          ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
            (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K) ≫
          (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
            ((Sheaf.derivedRestrictScalars (ProEt.topology X)
              (finiteDualizingQuotient l E hmn)).obj K) ≫
          (normalizedDVRRes l E X hrm).map
            ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app K) := by
  sorry
end WeilConjectures
