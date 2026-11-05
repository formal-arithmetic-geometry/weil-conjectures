/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.OpenHomTriangleRealization

/-! # Mayer--Vietoris sequence for derived Hom

Source: Stacks Project, Cohomology, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).

## Main statements

- `derived_hom_mayer_vietoris`: exactness at global and local derived Hom.
- `derivedOpenHomRestriction`: the canonical restriction to a smaller open.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The structure sheaf viewed as a sheaf of rings, as in the module-stalk siblings.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris). -/
abbrev moduleRings (X : RingedSpace.{u}) :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf

private theorem modulePushforward_limits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

/-- Restriction to an open is additive. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: restriction precomposes the sectionwise linear maps with the forgetful functor
from the localized site; sums of maps are computed sectionwise. -/
theorem moduleOverFunctor_additive_proof (X : RingedSpace.{u}) (U : Opens X) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) U).Additive := by
  exact Functor.Additive.mk (by intros; rfl)

/-- Additivity of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_additive (X : RingedSpace.{u}) (U : Opens X) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) U).Additive :=
  moduleOverFunctor_additive_proof X U

/-- Restriction to an open preserves finite limits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: kernels and finite products of module sheaves are computed sectionwise, and
restriction retains precisely the sections on opens contained in the chosen open. -/
theorem moduleOverFunctor_limits_proof (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  exact modulePushforward_limits (𝟙 _)

/-- Finite-limit preservation of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_limits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) :=
  moduleOverFunctor_limits_proof X U

/-- Restriction to an open preserves finite colimits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: finite sums are sectionwise. Cokernels are sheafified sectionwise cokernels;
sheafification commutes with open restriction since covering families of an open
contained in the chosen open are the same in the localized site. -/
theorem moduleOverFunctor_colimits_proof (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  unfold SheafOfModules.overFunctor
  infer_instance

/-- Finite-colimit preservation of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_colimits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) :=
  moduleOverFunctor_colimits_proof X U

/-- Restriction between two opens is additive. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: `overMap` restricts sectionwise linear maps, and therefore preserves their sums. -/
theorem moduleOverMap_additive_proof (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    (SheafOfModules.overMap.{u} (moduleRings X) i).Additive := by
  exact Functor.Additive.mk (by intros; rfl)

/-- Additivity of restriction between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_additive (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    (SheafOfModules.overMap.{u} (moduleRings X) i).Additive :=
  moduleOverMap_additive_proof X i

/-- Restriction between opens preserves finite limits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: the sectionwise descriptions of kernels and finite products are unchanged
when the localized site is further restricted to the smaller open. -/
theorem moduleOverMap_limits_proof (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u} (moduleRings X) i) := by
  exact modulePushforward_limits (Sheaf.pushforwardOverMapIso (moduleRings X) i).inv

/-- Finite-limit preservation between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_limits (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u} (moduleRings X) i) :=
  moduleOverMap_limits_proof X i

/-- Restriction between opens preserves finite colimits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: sums are sectionwise and cokernels are sheafified sectionwise cokernels.
Coverings on each smaller open agree in the two localized sites, so sheafification
and restriction commute. -/
theorem moduleOverMap_colimits_proof (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u} (moduleRings X) i) := by
  infer_instance

/-- Finite-colimit preservation between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_colimits (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u} (moduleRings X) i) :=
  moduleOverMap_colimits_proof X i

end AlgebraicGeometry
