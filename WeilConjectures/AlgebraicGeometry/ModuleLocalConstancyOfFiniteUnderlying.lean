/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.FiniteOperationLocalConstancy
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Local constancy of module operations on finite locally constant sets

## References

* [Stacks, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module sheaf whose underlying sets are finite locally constant is locally constant
as a module sheaf. This does not assert finiteness of its constant models
(Stacks, Tags 0DV5 and 093S). -/
theorem module_localConstancy_of_finite_underlying
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteLocallyConstantSheafOfTypes
      ((sheafForget Y.smallEtaleTopology).obj F)) :
    IsLocallyConstantSheaf F := by
  rcases hF.1 with ⟨𝒰, h𝒰⟩
  exact module_operationCompatibleCover F _ rfl (fun Ω _ _ s ↦ hF.finite_sheafFiber Ω s)
    𝒰 h𝒰

end AlgebraicGeometry.Scheme
