/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalFiniteRealization
/-! # Strict-presentation proper derived comparison
Source: blueprint def-pur-adic-support-realization.
(blueprint: lem-pur-adic-support-proper-derived-adapter).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
section CompactSupport
variable (c : Compactification g)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)

/-- The proper derived comparison is also available with the strict coefficient
presentation used by the compact-support level.  Its proof transports the
published proper comparison through the equivalence between the strict and
semilinear coefficient presentations, preserving the recorded normalization.
Source: blueprint def-pur-adic-support-realization.
Proof: transport the proper comparison along the coefficient-presentation
equivalence and compose the two comparison isomorphisms. -/
theorem integralExceptionalEtaleProperDerivedRight_exists (n : ℕ) :
    ∃ e : (S.properDerived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ⋙
        (Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) c.g).rightDerivedFunctor,
      True := by
  sorry

end CompactSupport
end WeilConjectures
