/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Multiplication by an integer and symmetric invertible modules

For a group scheme `G` over a field `K` (for instance an abelian variety) and an integer `n`,
multiplication by `n` is the morphism `[n] : G ⟶ G`, the `n`-th power of the identity in the group
`G ⟶ G`. An `𝒪_A`-module `L` on an abelian variety `A` (typically an invertible one) is
*symmetric* if `[-1]^* L ≅ L`.

## Main definitions

- `AlgebraicGeometry.multiplicationBy`: multiplication by an integer `n`, `[n] : G ⟶ G`.
- `AlgebraicGeometry.Scheme.Modules.IsSymmetric`: `[-1]^* L ≅ L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `definition-abelian-variety--2`: multiplication by an integer.

For a group scheme `G` over `K` (for instance an abelian variety) and an integer `n`,
multiplication by `n` is the morphism `[n] : G ⟶ G` given by the `n`-th power `𝟙 G ^ n` of the
identity in the group `G ⟶ G` of `CategoryTheory.GrpObj.Hom.group`; on `T`-valued points it is
`a ↦ a ^ n`, that is `a ↦ n • a` written additively (`AlgebraicGeometry.comp_multiplicationBy`).
For `n` a natural number this is the morphism `𝟙 G ^ n` used throughout
(`AlgebraicGeometry.multiplicationBy_natCast`), and `[-1]` is the inverse `ι[G]`
(`AlgebraicGeometry.multiplicationBy_neg_one`). -/
noncomputable def multiplicationBy (G : Over (Spec (.of K))) [GrpObj G] (n : ℤ) : G ⟶ G :=
  𝟙 G ^ n

variable (G : Over (Spec (.of K))) [GrpObj G]

/-- On `T`-valued points, `[n]` is `a ↦ a ^ n`. -/
theorem comp_multiplicationBy {T : Over (Spec (.of K))} (a : T ⟶ G) (n : ℤ) :
    a ≫ multiplicationBy G n = a ^ n := by
  rw [multiplicationBy, GrpObj.comp_zpow, Category.comp_id]

@[simp]
theorem multiplicationBy_natCast (n : ℕ) : multiplicationBy G n = 𝟙 G ^ n :=
  zpow_natCast _ n

@[simp]
theorem multiplicationBy_neg_one : multiplicationBy G (-1) = ι[G] := by
  rw [multiplicationBy, zpow_neg_one, GrpObj.inv_eq_inv]

/-- Blueprint `definition-abelian-variety--4`: symmetric invertible sheaves.

An `𝒪_A`-module `L` on a group scheme `A` over `K` (typically an invertible sheaf on an abelian
variety) is *symmetric* if `[-1]^* L ≅ L`, where `[-1] = AlgebraicGeometry.multiplicationBy A (-1)`
is multiplication by `-1`, that is the inverse `ι[A]` (`isSymmetric_iff`). -/
def Scheme.Modules.IsSymmetric {A : Over (Spec (.of K))} [GrpObj A] (L : A.left.Modules) : Prop :=
  Nonempty (overPullback (multiplicationBy A (-1)) L ≅ L)

/-- An `𝒪_A`-module `L` is symmetric if and only if `ι[A]^* L ≅ L`. -/
theorem Scheme.Modules.isSymmetric_iff {A : Over (Spec (.of K))} [GrpObj A]
    (L : A.left.Modules) : L.IsSymmetric ↔ Nonempty (overPullback ι[A] L ≅ L) := by
  rw [IsSymmetric, multiplicationBy_neg_one]

end AlgebraicGeometry
