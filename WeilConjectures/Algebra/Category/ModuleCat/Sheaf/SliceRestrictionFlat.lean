/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Flatness under restriction to a slice site

## References

* Stacks Project, Modules on Sites, Tag 0E8J
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- Restricting a flat module sheaf to the slice site over any object preserves flatness. -/
theorem isFlat_over
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : C) (hF : IsFlat F) : IsFlat (R := R.over U) (F.over U)  := by
  let _ := SheafOfModules.monoidalCategory R
  let _ : MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
    SheafOfModules.monoidalCategory (R.over U)
  let _ : SymmetricCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
    SheafOfModules.symmetricCategory (R.over U)
  refine (exactFunctor_iff _).2 ⟨?_, ?_⟩
  · exact isFlat_over_preservesFiniteLimits F U hF
      (SheafOfModules.monoidalCategory (R.over U)) rfl
  · obtain ⟨_, ⟨closed⟩, _⟩ := SheafOfModules.tensorClosed (R.over U)
    let _ : MonoidalClosed (SheafOfModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) := closed
    exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

end SheafOfModules
