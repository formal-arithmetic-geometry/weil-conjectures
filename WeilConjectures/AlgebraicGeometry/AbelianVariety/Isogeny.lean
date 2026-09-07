/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.Mathlib.Topology.JacobsonSpace

/-!
# The multiplication by `n` isogeny of an abelian variety

Let `A` be an abelian variety of dimension `g` over a field `K`. Multiplication by `n` on the
group object `A` is an endomorphism `[n] : A ⟶ A`, here called
`AlgebraicGeometry.IsAbelianVariety.mulBy`. For `n ≠ 0` it is an *isogeny*: a finite, flat and
surjective morphism, of degree `n ^ (2 * g)`; and it is étale as soon as `n` is invertible in
`K`.

From surjectivity alone one gets that the group `A(K)` of `K`-points of `A` is `n`-divisible
when `K` is algebraically closed, since over an algebraically closed field the `K`-points of a
`K`-scheme locally of finite type are exactly its closed points, and a point lying over a closed
point along a finite morphism is again closed.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety.mulBy`: the multiplication by `n` endomorphism
  `[n] : A ⟶ A` of an abelian variety `A`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.isFinite_mulBy`,
  `AlgebraicGeometry.IsAbelianVariety.flat_mulBy` and
  `AlgebraicGeometry.IsAbelianVariety.surjective_mulBy` — for `n ≠ 0`, the morphism `[n]` is
  finite, flat and surjective, i.e. an isogeny.
- `AlgebraicGeometry.IsAbelianVariety.finrank_mulBy` — the isogeny `[n]` has degree
  `n ^ (2 * g)`, where `g` is the dimension of `A`.
- `AlgebraicGeometry.IsAbelianVariety.etale_mulBy` — if `n` is invertible in `K`, then `[n]` is
  étale.
- `AlgebraicGeometry.IsAbelianVariety.exists_npow_eq` and
  `AlgebraicGeometry.IsAbelianVariety.rootableBy` — if `K` is algebraically
  closed and `n ≠ 0`, then every `K`-point of `A` is an `n`-th power, i.e. the group `A(K)` is
  `n`-divisible.

## Implementation notes

* `isFinite_mulBy`, `flat_mulBy`, `surjective_mulBy`, `finrank_mulBy` and `etale_mulBy` are
  `sorry` by design: this file only *states* that `[n]` is an isogeny of degree `n ^ (2 * g)`
  which is étale in the good characteristic, and uses those statements. The missing ingredient
  for the first four is the theorem of the cube, which for a symmetric ample line bundle `L`
  gives `[n]^* L ≅ L ^ (n ^ 2)`; Mathlib has neither the theorem of the cube nor ampleness of
  line bundles nor intersection numbers. The missing ingredient for `etale_mulBy` is a theory of
  differentials for schemes, which Mathlib does not have either. See the classical proofs in the
  individual docstrings.
* The first four statements are owned by issue 776 ("Prove that `[n]` is an isogeny of degree
  `n ^ (2 * g)`: the theorem of the cube and the degree computation") and `etale_mulBy` by issue
  777 ("Prove that `[n]` is étale when `n` is prime to the characteristic").
* Following `WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian`, the dimension `g` of `A`
  is not a field of `IsAbelianVariety` but an instance argument
  `[SmoothOfRelativeDimension g G.hom]` at the use site.

## References

* D. Mumford, *Abelian Varieties*, §6.
* J. S. Milne, *Abelian Varieties*, I.7.

## Blueprint

The declarations of this file implement Proposition 2.7 (`mulBy`, `isFinite_mulBy`,
`flat_mulBy`, `surjective_mulBy`, `finrank_mulBy`), Proposition 2.8 (`etale_mulBy`, the input it
needs) and Proposition 2.9 (`exists_npow_eq`) of §2.6 of `blueprint/curve_estimates.pdf`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.IsAbelianVariety

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G]

/-- The multiplication by `n` endomorphism `[n] : A ⟶ A` of a group scheme `A` over a field,
i.e. the endomorphism `x ↦ xⁿ` of the underlying group object. For an abelian variety and
`n ≠ 0` this is an isogeny, see `AlgebraicGeometry.IsAbelianVariety.isFinite_mulBy`,
`AlgebraicGeometry.IsAbelianVariety.flat_mulBy` and
`AlgebraicGeometry.IsAbelianVariety.surjective_mulBy`. -/
noncomputable def mulBy (n : ℕ) : G ⟶ G := GrpObj.npow G n

@[simp]
lemma mulBy_left (n : ℕ) : (mulBy G n).left = (GrpObj.npow G n).left := rfl

variable [IsAbelianVariety G] {n : ℕ}

/-- The multiplication by `n` isogeny of an abelian variety is finite for `n ≠ 0`.

Classically: pick a symmetric ample line bundle `L` on `A`. The theorem of the cube gives
`[n]^* L ≅ L ^ (n ^ 2)`, which is again ample. The kernel of `[n]` is a closed subscheme on
which `[n]^* L` is trivial, so the restriction of an ample line bundle to it is trivial, which
forces it to be finite. Hence `[n]` is proper with finite fibres, so finite by Zariski's main
theorem (`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`).

This is `sorry` by design; see the implementation notes of this file and issue 776. -/
theorem isFinite_mulBy (hn : n ≠ 0) : IsFinite (mulBy G n).left :=
  sorry

/-- The multiplication by `n` isogeny of an abelian variety is flat for `n ≠ 0`.

Classically: `[n]` is a finite surjective morphism between smooth varieties of the same
dimension, hence flat by "miracle flatness".

This is `sorry` by design; see the implementation notes of this file and issue 776. -/
theorem flat_mulBy (hn : n ≠ 0) : Flat (mulBy G n).left :=
  sorry

/-- The multiplication by `n` isogeny of an abelian variety is surjective for `n ≠ 0`.

Classically: by `AlgebraicGeometry.IsAbelianVariety.isFinite_mulBy` the image of `[n]` is a
closed subgroup scheme of `A` of the same dimension as `A`, and `A` is connected, so the image
is all of `A`.

This is `sorry` by design; see the implementation notes of this file and issue 776. -/
theorem surjective_mulBy (hn : n ≠ 0) : Surjective (mulBy G n).left :=
  sorry

/-- The multiplication by `n` isogeny of an abelian variety of dimension `g` has degree
`n ^ (2 * g)`.

Classically: for a symmetric ample line bundle `L` on `A`, the theorem of the cube gives
`[n]^* L ≅ L ^ (n ^ 2)`, so comparing self-intersection numbers,
`deg [n] * (L ^ g) = ([n]^* L) ^ g = n ^ (2 * g) * (L ^ g)`, and `L ^ g ≠ 0` by ampleness.

This is `sorry` by design; see the implementation notes of this file and issue 776. -/
theorem finrank_mulBy {g : ℕ} [SmoothOfRelativeDimension g G.hom] (hn : n ≠ 0) (x : G.left) :
    (mulBy G n).left.finrank x = n ^ (2 * g) :=
  sorry

/-- The multiplication by `n` isogeny of an abelian variety is étale if `n` is invertible in the
base field.

Classically: `[n]` is finite and flat, so it is étale as soon as it is unramified, and this can
be checked at the identity by translating. The differential of `[n]` at the identity is
multiplication by `n` on the tangent space, which is an isomorphism precisely when `n` is
invertible in `K`.

This is `sorry` by design; see the implementation notes of this file and issue 777. -/
theorem etale_mulBy (hn : (n : K) ≠ 0) : Etale (mulBy G n).left :=
  sorry

section IsAlgClosed

variable [IsAlgClosed K]

/-- **Divisibility of the group of points of an abelian variety.** If `K` is algebraically closed
and `n ≠ 0`, every `K`-point of an abelian variety over `K` is an `n`-th power; in other words
`A(K) / n · A(K) = 0`. -/
theorem exists_npow_eq (hn : n ≠ 0) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    ∃ y : 𝟙_ (Over (Spec (.of K))) ⟶ G, y ^ n = x := by
  have := isFinite_mulBy G hn
  have := surjective_mulBy G hn
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  set f : G.left ⟶ G.left := (mulBy G n).left with hf
  -- the `K`-point `x` is a section of `G.hom`, hence a closed point `x₀` of `G.left`
  have hxw : (x.left : Spec (.of K) ⟶ G.left) ≫ G.hom = 𝟙 _ := Over.w x
  have hx₀ : IsClosed {x.left (IsLocalRing.closedPoint K)} :=
    ((pointEquivClosedPoint G.hom) ⟨x.left, hxw⟩).2
  -- `[n]` is surjective, so `x₀` has a preimage `z`
  obtain ⟨z, hz⟩ := f.surjective (x.left (IsLocalRing.closedPoint K))
  -- `z` is closed, since the fibre of the finite morphism `[n]` over `x₀` is finite and closed
  have hzc : IsClosed {z} :=
    (f.finite_preimage_singleton _).subset_closedPoints (hx₀.preimage f.continuous) hz
  -- turn the closed point `z` back into a `K`-point `y` of `G`
  refine ⟨Over.homMk (pointOfClosedPoint G.hom z hzc)
    (pointOfClosedPoint_comp G.hom z hzc), ?_⟩
  rw [← GrpObj.comp_npow]
  apply Over.OverMorphism.ext
  change pointOfClosedPoint G.hom z hzc ≫ f = x.left
  refine ext_of_apply_closedPoint_eq G.hom ?_ hxw ?_
  · rw [Category.assoc, hf, Over.w (mulBy G n), pointOfClosedPoint_comp]
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
    exact hz

/-- The group of `K`-points of an abelian variety over an algebraically closed field `K` is
divisible. -/
noncomputable instance rootableBy : RootableBy (𝟙_ (Over (Spec (.of K))) ⟶ G) ℕ :=
  rootableByOfPowLeftSurj _ _ fun hn x ↦ exists_npow_eq G hn x

end IsAlgClosed

end AlgebraicGeometry.IsAbelianVariety
