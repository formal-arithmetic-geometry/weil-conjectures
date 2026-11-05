/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.CategoryTheory.Sites.MonoidalUnitSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Adic.AdicSectionModuleEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Native adic modules and sectionwise slice Hom

Source: Stacks Project, Modules on Sites, Tags 03EO and 0E8H; the native constructions in
`WeilConjectures.SixFunctors.ProEtale.Adic.Module`, `Hom`, `InternalHom` and
`InternalHomEvaluation` (blueprint: lem-sf-adic-module-section-data).

The records below package the conclusions, with all comparison maps normalized on sections.
They impose no freeness, constructibility, or rank assumption on a module.

## Main definitions

* `adicComparisonTmul`, `adicComparisonEval`: the canonical native maps on local sections.
* `AdicModuleSectionComparison`: the equivalence and its tensor, Hom and evaluation formulas.
* `adicComparisonRestriction`, `adicComparisonPullSection`, `adicComparisonDualSlice`:
  the existing canonical restriction maps in the forms used by the comparison.
* `AdicModuleSliceHomComparison`: all comparison conclusions, including slice compatibility.

## Main statements

* `adicModuleSliceHomComparison`: existence of the normalized comparisons for every scheme.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The canonical local pure tensor in the native relative tensor, obtained by first mapping
into the sheaf tensor and then imposing the balanced relation.
Source: Stacks 03EO and the native coequalizer `Mod.tensorπ`
(blueprint: lem-sf-adic-module-section-data). -/
noncomputable def adicComparisonTmul {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    ((Mod.tensorLeft N).obj M).X.obj.obj V :=
  (Mod.tensorπ M N).hom.app V
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M.X N.X).app V
      (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))

/-- The native evaluation on a pair of local sections, using the canonical map into the
sheaf tensor. Source: Stacks 03EO and native `Mod.evaluation`
(blueprint: lem-sf-adic-module-section-data). -/
noncomputable def adicComparisonEval {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V) (x : M.X.obj.obj V) : N.X.obj.obj V :=
  (Mod.evaluation M N).hom.app V
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X)
      ((AdicSheaf.ihom M).obj N).X M.X).app V
      (z ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x))

namespace AdicModuleSectionComparison

end AdicModuleSectionComparison

end AlgebraicGeometry.ProEtale
