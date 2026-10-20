/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback

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
    (derivedPullback f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj ((pullback f).obj M) := by
  letI := canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let t := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  exact ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app M)) ≫
    (DerivedCategory.singleFunctor _ 0).map (t.hom.app M)

/-- The pinned comparison is invertible on an invertible module.
Source: Stacks, Tags 06YD and 06YJ
(blueprint: lem-pc-canonical-single-pullback-comparison).

Proof: An invertible module is quasi-coherent and intrinsically flat, including on
an empty scheme. The single complex is bounded above and termwise flat. The
left-derived counit is therefore invertible on it. Apply the canonical flat-module
comparison theorem to this counit; compose with the single embedding of the unique
adjunction-preserving tensor-pullback comparison, which is an isomorphism. -/
theorem isIso_canonicalSinglePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    IsIso (canonicalSinglePullbackMap f M) := by
  let := canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let c := ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app M))
  have hc : IsDerivedModulePullbackComparison f M c := by
    refine ⟨ε, ?_, rfl⟩
    exact (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  have : IsIso c := isIso_modulePullbackComparison_of_isFlatOver_identity f M
    (isFlatOver_of_isInvertible (𝟙 Y) M) c hc
  let t := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  have hi : IsIso (c ≫ (DerivedCategory.singleFunctor _ 0).map (t.hom.app M)) :=
    inferInstance
  simpa only [canonicalSinglePullbackMap, c, t, ε, Category.assoc] using hi

end AlgebraicGeometry.Scheme.Modules
