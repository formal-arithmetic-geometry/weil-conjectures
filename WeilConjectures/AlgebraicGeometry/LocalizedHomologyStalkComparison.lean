/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian

/-! # Exact localized stalks and their derived homology comparison

## References

* [Stacks, Tag 01AF](https://stacks.math.columbia.edu/tag/01AF)
* [Stacks, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace AlgebraicGeometry

/-- The additive stalk functor on the localized module site, through the canonical
module equivalence with the open subscheme. (Stacks, Tag 0098) -/
noncomputable def localizedModuleStalk (S : Scheme.{u}) (U : S.Opens) (s : U.toScheme) :
    SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤ AddCommGrpCat.{u} :=
  (Scheme.Modules.overEquiv U).functor ⋙
    Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ s

private instance schemeStalk_preservesFiniteLimits (S : Scheme.{u}) (s : S) :
    PreservesFiniteLimits (Scheme.Modules.toPresheaf S ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s) := by
  let T := SheafOfModules.toSheaf.{u} (moduleRings S.toRingedSpace)
  let F := TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s
  have : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s) := inferInstance
  change PreservesFiniteLimits (T ⋙ F)
  exact comp_preservesFiniteLimits T F

private instance schemeStalk_preservesFiniteColimits (S : Scheme.{u}) (s : S) :
    PreservesFiniteColimits (Scheme.Modules.toPresheaf S ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s) := by
  let T := SheafOfModules.toSheaf.{u} (moduleRings S.toRingedSpace)
  let F := TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s
  have : PreservesFiniteColimits T :=
    (CategoryTheory.moduleSheaves_colimits_forgetful (moduleRings S.toRingedSpace)).2.2.1
  have : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s) := inferInstance
  change PreservesFiniteColimits (T ⋙ F)
  exact comp_preservesFiniteColimits T F

/-- Localized stalks are exact, and restriction preserves every derived homology stalk
naturally in the derived object. (Stacks, Tags 01AF, 01AG, 0098) -/
theorem localized_homology_stalk_comparison (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (U : S.Opens) (s : U.toScheme) :
    (localizedModuleStalk S U s).Additive ∧
    PreservesFiniteLimits (localizedModuleStalk S U s) ∧
    PreservesFiniteColimits (localizedModuleStalk S U s) ∧
    ∀ n : ℤ, Nonempty
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n ⋙
        Scheme.Modules.toPresheaf S ⋙ TopCat.Presheaf.stalkFunctor _ s.val) ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) n ⋙
        localizedModuleStalk S U s)) := by
  have hlim : PreservesFiniteLimits (localizedModuleStalk S U s) :=
    comp_preservesFiniteLimits _ _
  have hcolim : PreservesFiniteColimits (localizedModuleStalk S U s) :=
    comp_preservesFiniteColimits _ _
  have hadd : (localizedModuleStalk S U s).Additive :=
    Functor.additive_of_preserves_binary_products _
  refine ⟨hadd, hlim, hcolim, ?_⟩
  intro n
  let r := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n
  let st := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ s
  let t : r ⋙ (Scheme.Modules.overEquiv U).functor ⋙ st ≅
      Scheme.Modules.toPresheaf S ⋙ TopCat.Presheaf.stalkFunctor _ s.val :=
    isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) st ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι s
  exact ⟨isoWhiskerLeft H t.symm ≪≫
    isoWhiskerRight (r.mapDerivedCategoryHomologyFunctorIso n)
      ((Scheme.Modules.overEquiv U).functor ⋙ st)⟩

end AlgebraicGeometry
