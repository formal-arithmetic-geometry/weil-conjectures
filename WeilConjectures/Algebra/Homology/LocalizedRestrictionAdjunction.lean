/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists

/-!
# Exact left adjunction for restriction to a localized ringed site

## References

* Stacks Project, Tags 03DI, 03DJ and 08FI
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For a sheaf of rings `R` on a Grothendieck site and an object `U`, assuming the
localized restriction functor preserves zero morphisms, there is a functor `G` from
localized `R`-module sheaves to `R`-module sheaves preserving finite limits and finite
colimits, together with an adjunction `G ⊣ restriction`, and the localized restriction
functor is additive. -/
theorem localized_restriction_adjunction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms) :
    ∃ (G : SheafOfModules.{max u v} (R.over U) ⥤ SheafOfModules.{max u v} R),
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      (SheafOfModules.overFunctor.{max u v} R U).Additive ∧
      Nonempty (G ⊣ SheafOfModules.overFunctor.{max u v} R U) := by
  obtain ⟨G, hlim, hcolim, hadj⟩ :=
    localized_restriction_extension_exists R U hzero
  refine ⟨G, hlim, hcolim, ?_, hadj⟩
  constructor
  intro X Y f g
  ext V x
  rfl

end CategoryTheory
