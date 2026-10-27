/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison

/-! # A named canonical normalized comparison family -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] moduleAbelianCohomologyLarge
  IsNormalizedCoherentEtaleComparison

/-- The family uniquely determined by the normalized comparison theorem.
Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: def-weil-pbc-affine-normalized-comparison-family). -/
@[irreducible] def affineNormalizedComparisonFamily (X : Scheme.{u})
    [CompactSpace X] [Scheme.IsSeparated X] :
    ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf F) q :=
  Classical.choose (exists_unique_qcoherentNormalizedComparison X)

/-- The named family has the prescribed normalization.
Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: def-weil-pbc-affine-normalized-comparison-family).
Proof: unfold the family and take the normalization field of its chosen specification. -/
theorem affineNormalizedComparisonFamily_normalized (X : Scheme.{u})
    [CompactSpace X] [Scheme.IsSeparated X] :
    IsNormalizedCoherentEtaleComparison X
      (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans
        (affineNormalizedComparisonFamily X F q)) := by
  unfold affineNormalizedComparisonFamily
  exact (Classical.choose_spec (exists_unique_qcoherentNormalizedComparison X)).1.1

end
end AlgebraicGeometry.Scheme.Modules
