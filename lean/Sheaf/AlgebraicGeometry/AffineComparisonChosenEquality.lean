/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
public import Sheaf.AlgebraicGeometry.AffineNormalizedComparisonFamily

/-! # The chosen normalized affine comparison -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The affine comparison is the inverse of the chosen normalized family.
Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: lem-weil-pbc-affine-comparison-chosen-equality).
Proof: this is the defining equation of `affineRealizationComparison`. -/
theorem affineRealizationComparison_eq_chosen (Y : Scheme.{u})
    [CompactSpace Y] [Y.IsSeparated] (F : Y.Modules) [F.IsQuasicoherent] (q : ℕ) :
    affineRealizationComparison Y F q =
      (Classical.choose (exists_unique_qcoherentNormalizedComparison Y) F q).symm := by
  unfold affineRealizationComparison
  rfl

/-- The affine comparison is the inverse of the named uniquely normalized family.
Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: lem-weil-pbc-affine-comparison-chosen-equality).
Proof: unfold the named family and use the inverse-choice equation for
affineRealizationComparison. -/
theorem affineRealizationComparison_eq_family (Y : Scheme.{u})
    [CompactSpace Y] [Y.IsSeparated] (F : Y.Modules) [F.IsQuasicoherent] (q : ℕ) :
    affineRealizationComparison Y F q = (affineNormalizedComparisonFamily Y F q).symm := by
  unfold affineNormalizedComparisonFamily
  exact affineRealizationComparison_eq_chosen Y F q

end
end AlgebraicGeometry.Scheme.Modules
