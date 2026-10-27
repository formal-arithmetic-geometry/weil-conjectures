/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! Intrinsic identity coherence for finite dualizing restriction. -/

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

/-- The intrinsic realization restriction comparison is normalized at the identity.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
identity normalization of the intrinsic comparison.
(blueprint: lem-coef-dualizing-realization-restriction-unit-intrinsic)

The identity quotient is identified with the identity ring map.  The ordinary
section-normalized comparison is transported through exact localization; its
inverse followed by the canonical identity maps on both derived sites agrees
with the identity-normalized comparison on the pro-etale site. -/
theorem finiteDualizingIntrinsicRestriction_unit (n : ℕ) :
    (finiteDualizingIntrinsicRestriction l E X (le_refl n)).symm ≪≫
        Functor.isoWhiskerLeft
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor
          (normalizedDVRResUnit l E X n) ≪≫
        Functor.rightUnitor _ =
      Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso
            (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology X)
              (finiteDualizingQuotient l E (le_refl n))
              (by rw [finiteDualizingQuotient_id l E n])) ≪≫
            Functor.mapDerivedCategoryIdIso _)
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor ≪≫
        Functor.leftUnitor _ := by
  sorry

end WeilConjectures
