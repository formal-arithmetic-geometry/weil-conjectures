/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback

/-! # The pinned derived pullback comparison on a single module

Source: Stacks Project, Tags 06YD, 06YJ and 08HY.
(blueprint: lem-pc-canonical-single-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The additive structure used in the canonical derived composition comparisons.
Source: Stacks, Tag 0D5S (blueprint: lem-pc-canonical-single-pullback-comparison). -/
abbrev canonicalTensorPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorPullback f).Additive :=
  (Classical.choose exists_derivedPullbackComposition) f

/-- The specified derived counit, followed by the single-complex comparison and the
unique comparison of the two left adjoints to module pushforward.
Source: Stacks, Tags 06YJ and 08HY
(blueprint: lem-pc-canonical-single-pullback-comparison). -/
def canonicalSinglePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (AlgebraicGeometry.derivedPullback f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj ((pullback f).obj M) := by
  letI := canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let t := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  exact cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app M))) ≫
    (DerivedCategory.singleFunctor _ 0).map (t.hom.app M)

end AlgebraicGeometry.Scheme.Modules
