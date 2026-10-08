/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-!
# The multiplication-by-`n` isogeny

Multiplication by `n` on an abelian scheme `A` over a base `S` is a finite flat surjective
homomorphism, hence an isogeny, and its kernel `A[n]` is a finite flat group scheme over `S`.
At a point `s` of `S` over which `A` has relative dimension `g`, the isogeny has degree
`n ^ (2 * g)`, the rank of `A[n]` at `s`; on points over an algebraically closed field
multiplication by `n` is surjective, so `A(K)` is a divisible group.

Multiplication by `n` is written `𝟙 A ^ n`, the `n`-th power of the identity in the group
`A ⟶ A` coming from `CategoryTheory.GrpObj.Hom.group`.

The statements over a general base come first, those needing a field (the order of a finite
group scheme is only defined there) after them.

## Main statements

- `AlgebraicGeometry.isFinite_npow_id`, `AlgebraicGeometry.surjective_npow_id`: multiplication
  by `n` is finite and surjective.
- `AlgebraicGeometry.IsIsogeny.isFinite`, `AlgebraicGeometry.IsIsogeny.flat`,
  `AlgebraicGeometry.IsIsogeny.finrank_eq`: an isogeny is finite flat, and its degree as a
  finite flat morphism is the rank of its kernel.
- `AlgebraicGeometry.isIsogeny_npow_id`, `AlgebraicGeometry.isogenyDegreeAt_npow_id`,
  `AlgebraicGeometry.isogenyDegree_npow_id`: multiplication by `n` is an isogeny, of degree
  `n ^ (2 * g)` where `g` is the relative dimension, in particular over a field.
- `AlgebraicGeometry.isFinite_torsionSubgroupScheme`,
  `AlgebraicGeometry.flat_torsionSubgroupScheme`,
  `AlgebraicGeometry.finrank_torsionSubgroupScheme`: `A[n]` is finite flat, of rank
  `n ^ (2 * g)` at a point over which `A` has relative dimension `g`.
- `AlgebraicGeometry.surjective_npow_points`: `A(K)` is divisible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

section Base

variable {S : Scheme.{u}}

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

Let `A` be an abelian scheme over a base `S` and `0 < n`. Then `[n] : A ⟶ A` is finite. -/
theorem isFinite_npow_id (A : Over S) [GrpObj A] [IsAbelianScheme A] (n : ℕ) (hn : 0 < n) :
    IsFinite (𝟙 A ^ n).left :=
  sorry

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

The kernel `A[n] = ker [n]` of multiplication by `0 < n` on an abelian scheme over `S` is a
finite group scheme over `S`. -/
theorem isFinite_torsionSubgroupScheme (A : Over S) [GrpObj A] [IsAbelianScheme A] (n : ℕ)
    (hn : 0 < n) :
    IsFinite (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

Let `A` be an abelian scheme over a base `S` and `0 < n`. Then `[n] : A ⟶ A` is surjective, so
`A` is a divisible group scheme. -/
theorem surjective_npow_id (A : Over S) [GrpObj A] [IsAbelianScheme A] (n : ℕ) (hn : 0 < n) :
    Surjective (𝟙 A ^ n).left :=
  sorry

variable {A B : Over S} [GrpObj A] [GrpObj B] [IsAbelianScheme A] [IsAbelianScheme B]

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

An isogeny of abelian schemes is a finite morphism. -/
theorem IsIsogeny.isFinite (f : A ⟶ B) [IsIsogeny f] : IsFinite f.left :=
  sorry

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

An isogeny of abelian schemes is a flat morphism. -/
theorem IsIsogeny.flat (f : A ⟶ B) [IsIsogeny f] : Flat f.left :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Let `A` be an abelian scheme over a base `S` and let `0 < n`. Then `[n] : A ⟶ A` is a finite
flat surjective homomorphism, hence an isogeny. -/
theorem isIsogeny_npow_id (n : ℕ) (hn : 0 < n) : IsIsogeny (𝟙 A ^ n) :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian scheme is flat over the base for `0 < n`. -/
theorem flat_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) :
    Flat (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

For an isogeny `f : A ⟶ B` of abelian schemes over `S` and a point `y` of `B` over `s : S`, the
rank of the finite flat morphism `f` at `y` is the rank of its kernel at `s`: the fibre of `f`
at `y` is a torsor under the fibre of `ker f` at `s`. -/
theorem IsIsogeny.finrank_eq (f : A ⟶ B) [IsIsogeny f] (y : B.left) :
    f.left.finrank y = isogenyDegreeAt f (B.hom y) :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Multiplication by `0 < n` on an abelian scheme `A` over `S` has degree `n ^ (2 * g)` at a point
`s` of `S`, where `g = IsAbelianScheme.dimAt A s` is the dimension of the fibre of `A` at `s`. -/
theorem isogenyDegreeAt_npow_id (n : ℕ) (hn : 0 < n) (s : S) :
    isogenyDegreeAt (𝟙 A ^ n) s = n ^ (2 * IsAbelianScheme.dimAt A s) :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian scheme `A` over `S` has rank `n ^ (2 * g)` at a point `s` of `S`
over which `A` has relative dimension `g`, for `0 < n`: the rank of `A[n] = ker [n]` at `s` is
the degree of the isogeny `[n]` at `s`. -/
theorem finrank_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) (s : S) :
    (torsionSubgroupScheme A n).hom.finrank s = n ^ (2 * IsAbelianScheme.dimAt A s) :=
  isogenyDegreeAt_npow_id n hn s

end Base

section Field

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

The `n`-torsion of an abelian variety is zero-dimensional for `0 < n`. -/
theorem topologicalKrullDim_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianScheme A] (n : ℕ) (hn : 0 < n) :
    topologicalKrullDim (torsionSubgroupScheme A n).left = 0 :=
  sorry

variable {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] [IsAbelianScheme A]
  [IsAbelianScheme B]

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Multiplication by `0 < n` on an abelian variety of dimension `g` has degree `n ^ (2 * g)`. -/
theorem isogenyDegree_npow_id (n : ℕ) (hn : 0 < n) :
    isogenyDegree (𝟙 A ^ n) = n ^ (2 * IsAbelianScheme.dim A) :=
  isogenyDegreeAt_npow_id n hn _

/-- Blueprint `sk-prop-av-divisible`: Surjectivity of multiplication by `n` on points.

Let `A` be an abelian variety over an algebraically closed field `K` and `0 < n`. Then
`[n] : A(K) ⟶ A(K)` is surjective: `A(K)` is a divisible abelian group. -/
theorem surjective_npow_points [IsAlgClosed K] (n : ℕ) (hn : 0 < n) :
    Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A ↦ a ^ n :=
  sorry

end Field

end AlgebraicGeometry
