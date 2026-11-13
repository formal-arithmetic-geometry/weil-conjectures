/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback

/-! # Canonical derived base change for a flat family and a line bundle

Source: Stacks Project, Tag 0A1D (base change for relatively flat complexes).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical derived base-change map at a line bundle on a flat qc separated family
is invertible, without a hypothesis on its higher direct images.

Source: Stacks Project, Tag 0A1D. -/
theorem isIso_derivedBaseChange_of_flat_invertible
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [Flat f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g)
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) := by
  let F := Scheme.Modules.tensorPullback g'
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g'
  let : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : F.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ F
    (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  obtain ⟨c, hc, hbc⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    f g g' f' sq M (isFlatOver_of_isInvertible f M)
  have : IsIso c := isIso_modulePullbackComparison_of_isFlatOver_identity
    g' M (isFlatOver_of_isInvertible (𝟙 X) M) c hc
  have := hbc
  exact (isIso_comp_right_iff _ ((schemeDerivedDirectImage f').map c)).mp hbc

end AlgebraicGeometry.Scheme.Modules
