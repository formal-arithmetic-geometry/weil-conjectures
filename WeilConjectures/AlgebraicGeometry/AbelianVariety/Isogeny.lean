/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs

/-!
# The multiplication-by-`n` isogeny

Multiplication by `n` on an abelian variety `A` of dimension `g` is a finite flat surjective
homomorphism, hence an isogeny, of degree `n ^ (2 * g)`, and its kernel `A[n]` is a finite flat
group scheme of that order. On points over an algebraically closed field it is surjective, so
`A(K)` is a divisible group.

Multiplication by `n` is written `𝟙 A ^ n`, the `n`-th power of the identity in the group
`A ⟶ A` coming from `CategoryTheory.GrpObj.Hom.group`.

## Main statements

- `AlgebraicGeometry.isMonHom_npow_id`: the `n`-fold sum is a homomorphism.
- `AlgebraicGeometry.isFinite_npow_id`: multiplication by `n` has finite fibres.
- `AlgebraicGeometry.surjective_npow_id`: multiplication by `n` is surjective.
- `AlgebraicGeometry.finrank_eq_isogenyDegree`: the degree of an isogeny is the order of its
  kernel.
- `AlgebraicGeometry.isIsogeny_npow_id`: multiplication by `n` is an isogeny of degree
  `n ^ (2 * g)`.
- `AlgebraicGeometry.surjective_npow_points`: `A(K)` is divisible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-hom`: The `n`-fold sum is a homomorphism.

Let `G` be a commutative group scheme over `K` and `n ≥ 1`. Then the `n`-fold sum map
`[n] : G ⟶ G` is a homomorphism of group schemes. -/
theorem isMonHom_npow_id (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom (𝟙 G ^ n) :=
  sorry

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

Let `A` be an abelian variety over `K` and `n ≥ 1`. Then `[n] : A ⟶ A` is finite; in particular
`A[n] = ker [n]` is a finite group scheme. -/
theorem isFinite_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 1 ≤ n) :
    IsFinite (𝟙 A ^ n).left ∧ IsFinite (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

Let `A` be an abelian variety of dimension `g` over `K` and `n ≥ 1`. Then `[n] : A ⟶ A` is
surjective, so `A` is a divisible group scheme and `dim A[n] = 0`. -/
theorem surjective_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 1 ≤ n) :
    Surjective (𝟙 A ^ n).left ∧ topologicalKrullDim (torsionSubgroupScheme A n).left = 0 :=
  sorry

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

Let `f : A ⟶ B` be an isogeny of abelian varieties with kernel of order `d`. Then `f` is finite
and flat and `f_* 𝒪_A` is locally free of rank `d`: the degree of the finite flat morphism `f`
equals the order of its kernel. -/
theorem finrank_eq_isogenyDegree (A B : Over (Spec (.of K))) [GrpObj A] [GrpObj B]
    [IsAbelianVariety A] [IsAbelianVariety B] (f : A ⟶ B) (hf : IsIsogeny f) :
    IsFinite f.left ∧ Flat f.left ∧ ∀ y : B.left, f.left.finrank y = isogenyDegree f :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Let `A` be an abelian variety of dimension `g` over `K` and let `n ≥ 1`. Then `[n] : A ⟶ A` is a
finite flat surjective homomorphism, hence an isogeny, of degree `n ^ (2 * g)`, and its kernel
`A[n]` is a finite flat group scheme over `K` of order `n ^ (2 * g)`. -/
theorem isIsogeny_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (g n : ℕ)
    (hg : topologicalKrullDim A.left = (g : ℕ∞)) (hn : 1 ≤ n) :
    IsIsogeny (𝟙 A ^ n) ∧ Flat (𝟙 A ^ n).left ∧ isogenyDegree (𝟙 A ^ n) = n ^ (2 * g) ∧
      IsFinite (torsionSubgroupScheme A n).hom ∧ Flat (torsionSubgroupScheme A n).hom ∧
      (torsionSubgroupScheme A n).hom.finrankΓ = n ^ (2 * g) :=
  sorry

/-- Blueprint `sk-prop-av-divisible`: Surjectivity of multiplication by `n` on points.

Let `A` be an abelian variety over an algebraically closed field `K` and `n ≥ 1`. Then
`[n] : A(K) ⟶ A(K)` is surjective: `A(K)` is a divisible abelian group. -/
theorem surjective_npow_points [IsAlgClosed K] (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A => a ^ n :=
  sorry

end AlgebraicGeometry
