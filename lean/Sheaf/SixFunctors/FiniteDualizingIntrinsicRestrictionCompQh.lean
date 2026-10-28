/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.FiniteDualizingData

/-! Qh-object case of intrinsic finite-dualizing restriction composition. -/
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

/-- The composition comparison on the image of the homotopy-category localization.
Source: the comparison pasting step of the intrinsic restriction composition proof
(blueprint: lem-coef-dualizing-intrinsic-restriction-comp-qh-x7).

The assertion is the section-normalized comparison on a representative complex;
localization and exactness are handled by the parent theorem. -/
theorem finiteDualizingIntrinsicRestriction_comp_Qh
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (P : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat (finiteDualizingCoeff l E n))) ℤ) :
    (finiteDualizingIntrinsicRestriction l E X (hmn.trans hrm)).inv.app
        (DerivedCategory.Q.obj P) ≫
        (normalizedDVRResComp l E X hrm hmn).inv.app
          ((sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
            (DerivedCategory.Q.obj P)) =
      (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app
          (DerivedCategory.Q.obj P)) ≫
        (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
          ((Sheaf.derivedRestrictScalars (ProEt.topology X)
            (finiteDualizingQuotient l E hmn)).obj
            (DerivedCategory.Q.obj P)) ≫
        (normalizedDVRRes l E X hrm).map
          ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app
            (DerivedCategory.Q.obj P)) := by
  sorry
end WeilConjectures
