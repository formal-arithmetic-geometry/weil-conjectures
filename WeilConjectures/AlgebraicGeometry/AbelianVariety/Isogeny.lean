/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-!
# The multiplication-by-`n` isogeny

Multiplication by `n` on an abelian variety `A` of dimension `g` is a finite flat surjective
homomorphism, hence an isogeny, of degree `n ^ (2 * g)`, and its kernel `A[n]` is a finite flat
group scheme of that order. On points over an algebraically closed field it is surjective, so
`A(K)` is a divisible group.

Multiplication by `n` is written `𝟙 A ^ n`, the `n`-th power of the identity in the group
`A ⟶ A` coming from `CategoryTheory.GrpObj.Hom.group`.

## Main statements

- `AlgebraicGeometry.isFinite_npow_id`, `AlgebraicGeometry.surjective_npow_id`: multiplication
  by `n` is finite and surjective.
- `AlgebraicGeometry.IsIsogeny.isFinite`, `AlgebraicGeometry.IsIsogeny.flat`,
  `AlgebraicGeometry.IsIsogeny.finrank_eq`: an isogeny is finite flat of degree the order of
  its kernel.
- `AlgebraicGeometry.isIsogeny_npow_id`, `AlgebraicGeometry.isogenyDegree_npow_id`:
  multiplication by `n` is an isogeny of degree `n ^ (2 * g)`.
- `AlgebraicGeometry.isFinite_torsionSubgroupScheme`,
  `AlgebraicGeometry.flat_torsionSubgroupScheme`,
  `AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`: `A[n]` is finite flat of order
  `n ^ (2 * g)`.
- `AlgebraicGeometry.surjective_npow_points`: `A(K)` is divisible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

Let `A` be an abelian variety over `K` and `0 < n`. Then `[n] : A ⟶ A` is finite. -/
theorem isFinite_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 0 < n) :
    IsFinite (𝟙 A ^ n).left :=
  sorry

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

The kernel `A[n] = ker [n]` of multiplication by `0 < n` on an abelian variety is a finite
group scheme. -/
theorem isFinite_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (n : ℕ) (hn : 0 < n) :
    IsFinite (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

Let `A` be an abelian variety over `K` and `0 < n`. Then `[n] : A ⟶ A` is surjective, so `A` is
a divisible group scheme. -/
theorem surjective_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 0 < n) :
    Surjective (𝟙 A ^ n).left :=
  sorry

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

The `n`-torsion of an abelian variety is zero-dimensional for `0 < n`. -/
theorem topologicalKrullDim_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (n : ℕ) (hn : 0 < n) :
    topologicalKrullDim (torsionSubgroupScheme A n).left = 0 :=
  sorry

variable {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] [IsAbelianVariety A]
  [IsAbelianVariety B]

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

An isogeny of abelian varieties is a finite morphism. -/
theorem IsIsogeny.isFinite (f : A ⟶ B) [IsIsogeny f] : IsFinite f.left :=
  sorry

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

An isogeny of abelian varieties is a flat morphism. -/
theorem IsIsogeny.flat (f : A ⟶ B) [IsIsogeny f] : Flat f.left :=
  sorry

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

For an isogeny `f : A ⟶ B` of abelian varieties with kernel of order `d`, the sheaf `f_* 𝒪_A` is
locally free of rank `d`: the degree of the finite flat morphism `f` equals the order of its
kernel. -/
theorem IsIsogeny.finrank_eq (f : A ⟶ B) [IsIsogeny f] (y : B.left) :
    f.left.finrank y = isogenyDegree f :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Let `A` be an abelian variety over `K` and let `0 < n`. Then `[n] : A ⟶ A` is a finite flat
surjective homomorphism, hence an isogeny. -/
theorem isIsogeny_npow_id (n : ℕ) (hn : 0 < n) : IsIsogeny (𝟙 A ^ n) :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Multiplication by `0 < n` on an abelian variety of dimension `g` has degree `n ^ (2 * g)`. -/
theorem isogenyDegree_npow_id (n : ℕ) (hn : 0 < n) :
    isogenyDegree (𝟙 A ^ n) = n ^ (2 * IsAbelianVariety.dim A) :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian variety is flat over the base field for `0 < n`. -/
theorem flat_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) :
    Flat (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian variety of dimension `g` has order `n ^ (2 * g)` for `0 < n`. -/
theorem finrankΓ_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) :
    (torsionSubgroupScheme A n).hom.finrankΓ = n ^ (2 * IsAbelianVariety.dim A) :=
  sorry

/-- Blueprint `sk-prop-av-divisible`: Surjectivity of multiplication by `n` on points.

Let `A` be an abelian variety over an algebraically closed field `K` and `0 < n`. Then
`[n] : A(K) ⟶ A(K)` is surjective: `A(K)` is a divisible abelian group. -/
theorem surjective_npow_points [IsAlgClosed K] (n : ℕ) (hn : 0 < n) :
    Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A ↦ a ^ n :=
  sorry

end AlgebraicGeometry
