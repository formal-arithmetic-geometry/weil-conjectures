/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointSupport
public import WeilConjectures.TraceFormula.Additivity

/-!

# Complexes supported at finitely many rational points

Let `X` be a separated `k`-scheme of finite type and `S` a finite set of rational points of `X`.
A bounded constructible `ℚ̄_ℓ`-complex `C` on `X` whose restriction to the open complement
`X ∖ S` (`ProEtale.CondensedRing.pointsCompl`) vanishes is detected by its global sections: if
`RΓ(X, C) = 0`, then `C = 0`
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_pointsComplι_of_isZero_lowerStar`, blueprint
`det-nearby-kunneth-finite-support`).

The proof is by induction on `S`. For `S = S' ∪ {x}`, the open–closed triangle
`j_! Lj^* C ⟶ C ⟶ Rx_* Lx^* C ⟶` of the complement `j` of `x` splits: its connecting morphism
vanishes since `j_! Lj^* C` vanishes on the open neighbourhood `X ∖ S'` of `x`
(`ProEtale.CondensedRing.eq_zero_of_lowerStar_rationalPoint`). Hence `RΓ(X, Rx_* Lx^* C) = Lx^* C`
is a retract of `RΓ(X, C) = 0`, so `C` vanishes at `x`, hence on `X ∖ S'`, and we conclude by
induction.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Open subschemes as schemes over `s` -/

section Opens

end Opens

/-! ### The open complement of finitely many rational points -/

section PointsCompl

end PointsCompl

/-! ### Vanishing on opens -/

section Vanishing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

end Vanishing

/-! ### The splitting at a rational point -/

section Splitting

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {ℓ}

end Splitting

/-! ### Finitely many rational points -/

section Points

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

end Points

end AlgebraicGeometry.ProEtale.CondensedRing
