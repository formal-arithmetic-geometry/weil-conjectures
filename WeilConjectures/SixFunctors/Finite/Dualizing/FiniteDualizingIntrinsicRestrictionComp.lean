/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingIntrinsicRestrictionCompNatTrans
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingIntrinsicRestrictionCompQh

/-! # Intrinsic finite-coefficient restriction coherence -/

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

/-- Intrinsic successive restriction coherence.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
section-normalized intrinsic comparison part
(blueprint: lem-coef-dualizing-intrinsic-restriction-comp).

Proof: the intrinsic restriction comparison is characterized uniquely by its
values on scalar-unit sections. For a composite quotient, the two successive
comparisons and the direct comparison have the same values because quotient
maps compose on representatives. The uniqueness characterization transports
this equality through exact derived localization. Pasting with the canonical
normalized restriction compositor and the derived scalar-restriction
compositor gives the displayed component equation. -/
theorem finiteDualizingIntrinsicRestriction_comp
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat (finiteDualizingCoeff l E n)))) :
    (finiteDualizingIntrinsicRestriction l E X (hmn.trans hrm)).inv.app K ≫
        (normalizedDVRResComp l E X hrm hmn).inv.app
          ((sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K) =
      (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K) ≫
        (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
          ((Sheaf.derivedRestrictScalars (ProEt.topology X)
            (finiteDualizingQuotient l E hmn)).obj K) ≫
        (normalizedDVRRes l E X hrm).map
          ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app K) := by
  obtain ⟨rhs, hcomp, hrhs⟩ :=
    finiteDualizingIntrinsicRestriction_comp_natTrans_exists l E X hrm hmn
  have hcompK := congr_app hcomp K
  have hlhs :
      (finiteDualizingIntrinsicRestriction l E X (hmn.trans hrm)).inv.app K ≫
          (normalizedDVRResComp l E X hrm hmn).inv.app
            ((sfIntrinsicDerivedEquivalence X
              (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K) =
        (finiteDualizingIntrinsicRestrictionCompLhs l E X hrm hmn).app K := by
    rfl
  exact hlhs.trans (hcompK.trans (hrhs K))

end WeilConjectures
