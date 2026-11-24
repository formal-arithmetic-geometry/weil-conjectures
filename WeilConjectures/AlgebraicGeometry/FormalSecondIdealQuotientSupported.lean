/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAdic

/-! # Formal quotients by a second ideal

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The second-ideal quotient system is annihilated by the closed thickening's ideal
(Stacks, Tag 088A). -/
theorem formalSecondIdealQuotient_supported
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (e : ℕ) :
    ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (K ^ (e + 1)).subschemeι.ker.toModulesι
      (((M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)).obj (op n))) := by
  intro n
  rw [Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨p, hp⟩ := power_inclusion_iso K (e + 1) (Nat.succ_pos e)
  obtain ⟨d, _⟩ := product_inclusion_iso _ _ p hp
    (formalModuleQuotient K (e + 1) (M.obj.obj (op n)))
  exact d.isZero_iff.mp
    (idealModuleProduct_quotient_zero (Scheme.idealSheafPower K.toModulesι (e + 1)).2)

end AlgebraicGeometry
