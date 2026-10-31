/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingIntrinsicRestrictionCompQh

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

/-- Left side of the derived restriction composition identity.
Source: the inverse direct comparison followed by the normalized compositor
(blueprint: lem-coef-dualizing-intrinsic-restriction-comp). -/
noncomputable def finiteDualizingIntrinsicRestrictionCompLhs
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    Sheaf.derivedRestrictScalars (ProEt.topology X)
        (finiteDualizingQuotient l E (hmn.trans hrm)) ⋙
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (r + 1))).functor ⟶
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      normalizedDVRRes l E X hmn ⋙ normalizedDVRRes l E X hrm := by
  exact (finiteDualizingIntrinsicRestriction l E X (hmn.trans hrm)).inv ≫
    Functor.whiskerLeft
      ((sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).functor)
      (normalizedDVRResComp l E X hrm hmn).inv

end WeilConjectures
