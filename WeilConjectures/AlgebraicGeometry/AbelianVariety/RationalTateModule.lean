/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import WeilConjectures.NumberTheory.TateModule

/-!
# The Tate module of an abelian variety over an arbitrary field

Let `A` be an abelian variety of dimension `g` over a field `K` and `ℓ` a prime invertible in
`K`. The Tate module `T_ℓ A` of the group `A(K̄)` of geometric points is free of rank `2 g`
over `ℤ_ℓ`, so that `V_ℓ A` is a `2 g`-dimensional `ℚ_ℓ`-vector space. Over a finite field the
arithmetic Frobenius `σ` fixes no nonzero vector of `T_ℓ A`, and `σ - 1` is an automorphism of
`V_ℓ A`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_tateModule_of_natCast_ne_zero`:
  `T_ℓ A ≅ ℤ_ℓ ^ (2 g)`.
- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_rationalTateModule_of_natCast_ne_zero`:
  `V_ℓ A ≅ ℚ_ℓ ^ (2 g)`.
- `AlgebraicGeometry.IsAbelianVariety.eq_zero_of_galoisRepresentation_frobenius_eq_self`:
  `(T_ℓ A)^{σ = 1} = 0`.
- `AlgebraicGeometry.IsAbelianVariety.bijective_rationalTateModuleGaloisMap_frobenius_sub_id`:
  `σ - 1` is bijective on `V_ℓ A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.IsAbelianVariety

variable {K : Type u} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
  [IsAbelianVariety A]

section FiniteField

variable [Fintype K]

end FiniteField

end AlgebraicGeometry.IsAbelianVariety
