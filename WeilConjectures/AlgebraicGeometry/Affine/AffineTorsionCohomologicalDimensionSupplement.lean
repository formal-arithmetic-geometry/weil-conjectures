/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension

/-!
# Affine torsion cohomological dimension bound
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The affine finite-type step in the torsion cohomological-dimension bound.

Source: also
Stacks Project, Tag 0F0V (https://stacks.math.columbia.edu/tag/0F0V). -/
theorem subsingleton_H_of_two_mul_add_lt_of_isAffine {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    [IsAffine X] (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : d + c < q) : Subsingleton (Sheaf.H F q) := by
  exact hasTorsionCohomologicalDimensionLE_of_isAffine hK a hX F hF q hq

end AlgebraicGeometry.Scheme
