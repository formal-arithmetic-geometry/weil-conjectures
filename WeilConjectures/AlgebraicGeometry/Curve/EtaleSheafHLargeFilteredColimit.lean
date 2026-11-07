/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-! # Continuity of Ext cohomology for large filtered diagrams -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-pbc-u2-sheafH-large-filtered-colimit) -/
theorem sheafH_isColimit_large_filtered
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit ((Sheaf.functorH X.smallEtaleTopology q).mapCocone c)) := by
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso X q
  exact ⟨IsColimit.mapCoconeEquiv e.symm
    (etaleCohomology_isColimit_of_isFiltered_coefficientSize X hc q).some⟩

end AlgebraicGeometry.Scheme
