/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Topology.ProfiniteCondensedRing
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # Composite module pullback and its specified oplax mate

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL.

The left side uses the actual composite strong monoidal structure on mapMod followed
by extension of scalars. The right side uses the direct-image structure uniquely
normalized on local pure tensors, and the unit of the specified composite adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

/-- The actual composite oplax maps have the specified module-adjunction transposes
(Stacks, Tags 03D7 and 03EL). -/
theorem composite_module_oplax_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ M N : internalModules Λ Y,
      (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv (M ⊗ N)
          ((CondensedRing.upperStar Λ f).obj M ⊗ (CondensedRing.upperStar Λ f).obj N)
          ((CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N) =
        ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M ⊗ₘ
          (CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app N) ≫
          (internalPushLax Λ f).μ
            ((CondensedRing.upperStar Λ f).obj M) ((CondensedRing.upperStar Λ f).obj N)) ∧
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv
        (𝟙_ (internalModules Λ Y)) (𝟙_ (internalModules Λ X))
        (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.η =
      (internalPushLax Λ f).ε) := by
  -- The normalized direct image recovers the actual composite oplax structure.
  rw [← internalPullOplax_eq_canonical Λ f]
  constructor
  · intro M N
    exact ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _).apply_symm_apply _
  · exact ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _).apply_symm_apply _

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
