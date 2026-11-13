/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.Curve.ModuleSheafUnderlyingPreservesColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Colimits under the constant-coefficient module forgetful functor -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


/-- Forgetting constant-ring module structures preserves a module-sheaf colimit cocone.
Source: Stacks Project, Tags 03CO and 03CY. -/
theorem moduleSheaf_underlying_isColimit
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {A : Type (u + 1)} [SmallCategory A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {c : Cocone D} (hc : IsColimit c) :
    Nonempty (IsColimit ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapCocone c)) := by
  let _ := moduleSheaf_underlying_preserves_colimit (X := X) (Λ := Λ) (D := D)
  exact PreservesColimit.preserves hc

end AlgebraicGeometry.Scheme
