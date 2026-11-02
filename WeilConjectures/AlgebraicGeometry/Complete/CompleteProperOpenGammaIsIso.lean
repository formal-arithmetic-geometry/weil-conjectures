/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma

/-!
# Invertibility of the completed proper/open gamma

The proper/open comparison `cbcProperOpenGamma` on completed-ring modules is invertible
on complete objects with compatible bounded-below etale origins. The proof passes to the
strict quotient tower after constant-coefficient restriction, where the strict proper/open
gamma is invertible by finite compact-support base change.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The proper/open gamma is invertible on complete objects with compatible etale origins.
Source: blueprint proof step 8; Stacks 0F7B, 09C9 (blueprint: thm-cbc-complete-proetale). -/
theorem cbcProperOpenGamma_app_isIso {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (n : ℕ) (a : Fin n → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d V n a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins V d K.obj) :
    IsIso ((cbcProperOpenGamma d k r p i h).app K.obj) := by
  sorry

end AlgebraicGeometry.Scheme
