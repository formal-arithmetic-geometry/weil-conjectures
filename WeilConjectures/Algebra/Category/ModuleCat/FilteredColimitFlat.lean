/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat

/-!
# Filtered colimits of flat modules

A filtered colimit of flat modules over a commutative ring is flat.

## References

* Stacks Project, Algebra, Tag 05UT
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A filtered colimit of flat modules over a commutative ring is flat. -/
theorem filteredColimit_flat
    {R : Type u} [CommRing R]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{v} R) [HasColimit F]
    (hflat : ∀ i : I, Module.Flat R (F.obj i)) :
    Module.Flat R (colimit F : ModuleCat.{v} R) := by
  -- Move to a common universe without changing the module or the filtered colimit.
  let K := ModuleCat.uliftFunctor.{u, v} R
  have : PreservesColimitsOfShape I (forget (ModuleCat.{v} R)) := by
    change PreservesColimitsOfShape I
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat ⋙ forget AddCommGrpCat)
    infer_instance
  have : PreservesColimitsOfShape I (K ⋙ forget (ModuleCat.{max u v} R)) := by
    change PreservesColimitsOfShape I
      (forget (ModuleCat.{v} R) ⋙ CategoryTheory.uliftFunctor.{u})
    infer_instance
  have : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : PreservesColimitsOfShape I (forget (ModuleCat.{max u v} R)) := by
    change PreservesColimitsOfShape I
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat ⋙ forget AddCommGrpCat)
    infer_instance
  have : ReflectsColimitsOfShape I (forget (ModuleCat.{max u v} R)) := by
    exact ⟨fun {F} ↦ reflectsColimit_of_reflectsIsomorphisms F (forget (ModuleCat.{max u v} R))⟩
  have : PreservesColimitsOfShape I K :=
    preservesColimitsOfShape_of_reflects_of_preserves K (forget _)
  -- Lifting the ring makes the existing presentation theorem applicable.
  let L : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} (ULift.{v} R) :=
    ModuleCat.restrictScalars (ULift.ringEquiv (R := R)).toRingHom
  let D : AsSmall.{u} I ⥤ I := AsSmall.down
  have : D.IsEquivalence := (AsSmall.equiv (C := I)).isEquivalence_inverse
  let P : ColimitPresentation (AsSmall.{u} I) ((K ⋙ L).obj (colimit F)) :=
    ((ColimitPresentation.colimit F).map (K ⋙ L)).reindex D
  have h : Module.Flat (ULift.{v} R) ((K ⋙ L).obj (colimit F)) := by
    apply ModuleCat.flat_of_colimitPresentation P
    intro i
    have := hflat (D.obj i)
    change Module.Flat (ULift.{v} R) (ULift.{u} (F.obj (D.obj i)))
    rw [Module.Flat.ulift_left_iff]
    infer_instance
  -- Flatness is invariant under both lifts.
  change Module.Flat (ULift.{v} R) (ULift.{u} (colimit F : ModuleCat.{v} R)) at h
  exact Module.Flat.ulift_right_iff.mp (Module.Flat.ulift_left_iff.mp h)

end ModuleCat
