/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ModuleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveCechVanishing
import WeilConjectures.AlgebraicGeometry.ModuleSectionsAcyclicOfCohomologyVanishing

/-!
# Direct images of injective modules are acyclic on every open

## References

* [Stacks, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The direct image of an injective `𝒪_X`-module has zero positive module cohomology
on every open `V` of the target. Equivalently it is acyclic for the module-valued
sections functor `Γ(V,-)` (Stacks, Tags 01EX and 01E1). -/
theorem module_pushforward_injective_acyclic {X S : Scheme.{u}} (h : X ⟶ S)
    (I : X.Modules) [Injective I] :
    (∀ (V : S.Opens) (p : ℕ), 0 < p →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace p).obj
        ((restrictFunctor V.ι).obj ((pushforward h).obj I)))) ∧
    (∀ V : S.Opens,
      (SheafOfModules.forget.{u} S.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} S.ringCatSheaf.obj (op V)).rightAcyclic
        ((pushforward h).obj I)) := by
  have hcoh := module_cohomology_isZero_of_cech_vanishing.{u, u} S ((pushforward h).obj I)
    (module_pushforward_injective_cech_vanishing h I)
  exact ⟨hcoh, module_sections_acyclic_of_cohomology_vanishing S _ hcoh⟩

end AlgebraicGeometry.Scheme.Modules
