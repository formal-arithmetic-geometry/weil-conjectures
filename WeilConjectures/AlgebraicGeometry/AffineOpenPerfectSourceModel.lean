/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel

import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Perfect source models on affine opens

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-perfect-source-model).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- An exact equivalence transfers the size of a chosen derived localization. -/
private theorem localization_on_source {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  let : HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let d := e.mapDerivedCategory
  let : LocallySmall.{w} (DerivedCategory C) :=
    (locallySmall_congr d).mpr inferInstance
  exact ⟨(HomologicalComplex.quasiIso C (.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q⟩

end AlgebraicGeometry.Scheme
