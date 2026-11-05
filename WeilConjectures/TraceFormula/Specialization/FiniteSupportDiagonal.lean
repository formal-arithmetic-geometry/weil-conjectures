/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointsSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper

/-!

# Finite direct image is conservative where the diagonal is open

Let `f : Z ⟶ B` be a finite morphism of separated `k`-schemes of finite type and `F` a bounded
constructible `ℚ̄_ℓ`-complex on `Z` with `Rf_* F = 0`. By proper base change along `f`,
`Rp₁_* Lp₂^* F = 0` on `Z`, where `p₁, p₂ : Z ×_B Z ⟶ Z` are the projections. Over an open `V` of
`B` above which the diagonal `Δ : Z ⟶ Z ×_B Z` has open image, the open–closed triangle of `Δ`
splits, so that `F|_{f⁻¹ V} = LΔ^* Lp₂^* F|_{f⁻¹ V}` is a retract of `Rp₁_* Lp₂^* F|_{f⁻¹ V} = 0`
(`ProEtale.CondensedRing.isZero_upperStar_opensOverι_of_isOpen_range_diagonal`).

The splitting is `ProEtale.CondensedRing.isZero_upperStar_of_isZero_lowerStar_of_isOpen_range`:
a section `σ` of `p : W ⟶ Y` with open image satisfies `Lσ^* G = 0` whenever `Rp_* G = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Sections with open image -/

section Section

-- The last step identifies `Rp_* Rσ_*` with `R(σ ≫ p)_*`, which unfolds the pro-étale pullback.
set_option maxHeartbeats 400000 in -- see the comment above

end Section

/-! ### The fibre square of a finite morphism -/

section Diagonal

variable {Z B : Over (Spec (.of k))} (f : Z ⟶ B)

variable [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] [IsFinite f.left]

end Diagonal

end AlgebraicGeometry.ProEtale.CondensedRing
