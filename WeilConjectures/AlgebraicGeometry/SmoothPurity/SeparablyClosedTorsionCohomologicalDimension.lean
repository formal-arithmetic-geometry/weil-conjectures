/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Torsion cohomological dimension of a separably closed field

Source: Stacks Project, Tags 03QO, 04JQ and 04JM.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A separably closed field has torsion étale cohomological dimension at most zero.
Source: Stacks Project, Tags 03QO, 04JQ and 04JM. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] :
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 0 := by
  let Γ := CategoryTheory.Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Γ.PreservesEpimorphisms :=
    CategoryTheory.Functor.PreservesEpimorphisms.of_iso
      (CategoryTheory.Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtalePoint (k := K))).symm
  have := CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels Γ
  have : CategoryTheory.Limits.PreservesFiniteColimits Γ :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology Γ
  intro F _ q hq
  let e :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).mapIso
    (Γ.singleFunctorCompRightDerivedFunctorIso.app F)
  have hz := DerivedCategory.isZero_of_isLE
    ((DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} 0).obj (Γ.obj F))
    0 (q : ℤ) (by omega)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hz.of_iso e)

end AlgebraicGeometry.Scheme
