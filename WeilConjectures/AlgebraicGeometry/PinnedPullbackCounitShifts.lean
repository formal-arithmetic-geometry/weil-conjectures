/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Shifts compatible with the composition-pinned pullback counits

## References

* Stacks Project, Tags 08HY and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The left-derived counit selected by the composition theorem (Stacks, Tag 0D5S). -/
abbrev pinnedPullbackCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) f

/-- The composition-pinned left-derived counits admit compatible integer shifts
(Stacks, Tags 0D5S and 08HY). -/
theorem exists_pinned_pullback_counit_shifts
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive] :
    ∃ s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        letI := s f
        NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ  := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      ∃ s : (derivedPullback.{u, w} f).CommShift ℤ,
        letI := s
        NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ := by
    intro X Y f
    have hL := (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f
    exact Functor.rightKanExtension_coherentShift _ DerivedCategory.Qh
      (derivedPullback.{u, w} f) (pinnedPullbackCounit.{u, w} f)
      hL.isRightKanExtension
  refine ⟨fun f ↦ Classical.choose (h f), ?_⟩
  intro X Y f
  exact Classical.choose_spec (h f)

end AlgebraicGeometry
