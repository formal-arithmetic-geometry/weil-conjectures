/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The dimension of the homology of a short complex of vector spaces

For a short complex `X₁ ⟶ X₂ ⟶ X₃` of vector spaces with `X₂` finite dimensional, the dimension of
its homology is `dim X₂ - rank g - rank f`.
-/

@[expose] public section

open CategoryTheory Module

namespace CategoryTheory.ShortComplex

variable {K : Type*} [Field K] (S : ShortComplex (ModuleCat K)) [FiniteDimensional K S.X₂]

/-- `dim H(S) + rank g + rank f = dim X₂` for a short complex `S` of vector spaces with
`X₂` finite dimensional. -/
theorem finrank_homology_add_finrank_range_add_finrank_range :
    finrank K S.homology + finrank K (LinearMap.range S.g.hom) +
      finrank K (LinearMap.range S.f.hom) = finrank K S.X₂ := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) + _ + _ = _
  have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h₂ : finrank K (LinearMap.range S.moduleCatToCycles) =
      finrank K (LinearMap.range S.f.hom) := by
    have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom := by
      rintro _ ⟨x, rfl⟩
      exact congr($(S.zero) x)
    rw [LinearMap.range_codRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h₃ := LinearMap.finrank_range_add_finrank_ker S.g.hom
  omega

end CategoryTheory.ShortComplex
