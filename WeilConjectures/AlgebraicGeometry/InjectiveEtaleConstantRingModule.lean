/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence

/-!
# Realizing injective constant-coefficient sheaves as ringed-site modules

## References

* Stacks Project, Modules on Sites, Sections 093I and 03CV; Cohomology on Sites,
  Tags 03FC and 03FD.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An injective sheaf of constant-coefficient modules has an injective ringed-site
module realization with the same underlying abelian presheaf. -/
theorem exists_injective_etale_ring_module
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    ∃ (R : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (M : SheafOfModules.{u + 1} R), Injective M ∧
        Nonempty (M.val.presheaf ≅ J.obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  let F := etaleConstantModuleFunctor Y Λ
  let : F.IsEquivalence := etaleConstantModuleFunctor_isEquivalence Y Λ
  refine ⟨etaleConstantModuleRing Y Λ, F.obj J, ?_,
    ⟨etaleConstantModuleUnderlyingIso Y Λ J⟩⟩
  exact (F.asEquivalence.map_injective_iff J).mpr inferInstance

end AlgebraicGeometry.Scheme
