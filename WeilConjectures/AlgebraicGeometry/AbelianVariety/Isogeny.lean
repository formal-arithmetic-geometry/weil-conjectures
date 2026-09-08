/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.Group.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.Mathlib.Topology.Connected.Clopen
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
  `AlgebraicGeometry.IsAbelianVariety.surjective_mulBy` — for every `n ≠ 0`, the morphism `[n]`
  is finite, flat and surjective, i.e. an isogeny.
- `AlgebraicGeometry.IsAbelianVariety.finrank_mulBy` — the isogeny `[n]` has degree
  `n ^ (2 * g)`, where `g` is the dimension of `A`.
- `AlgebraicGeometry.IsAbelianVariety.etale_mulBy` — if `n` is invertible in `K`, then `[n]` is
  étale.
- `AlgebraicGeometry.IsAbelianVariety.isFinite_mulBy_of_natCast_ne_zero`,
  `AlgebraicGeometry.IsAbelianVariety.flat_mulBy_of_natCast_ne_zero` and
  `AlgebraicGeometry.IsAbelianVariety.surjective_mulBy_of_natCast_ne_zero` — the same three
  properties, but under the stronger hypothesis that `n` is invertible in `K`, and with a
  complete proof.
- `AlgebraicGeometry.IsAbelianVariety.exists_npow_eq` and
  `AlgebraicGeometry.IsAbelianVariety.exists_npow_eq_of_natCast_ne_zero` — if `K` is
  algebraically closed and `n ≠ 0` (resp. `n` is invertible in `K`), then every `K`-point of `A`
  is an `n`-th power, i.e. the group `A(K)` is `n`-divisible; see also
  `AlgebraicGeometry.IsAbelianVariety.rootableBy`.

## Implementation notes

* When `n` is invertible in `K`, everything except the degree formula is proved: étaleness,
  properness, finiteness, flatness and surjectivity of `[n]`, and `n`-divisibility of `A(K)`.
  The starting point is `etale_mulBy`, which is `AlgebraicGeometry.GrpObj.etale_npow_left`, an
  infinitesimal-lifting argument that needs no theory of differentials. The étale route sees no
  dimension, so it says nothing about the degree of `[n]`.
* Four statements are still `sorry`, and they are the only ones in this file.
  `isFinite_mulBy`, `flat_mulBy` and `surjective_mulBy` are open only in the bad characteristic:
  they are stated for every `n ≠ 0`, and the case `(n : K) ≠ 0` is the content of
  `isFinite_mulBy_of_natCast_ne_zero`, `flat_mulBy_of_natCast_ne_zero` and
  `surjective_mulBy_of_natCast_ne_zero`. `finrank_mulBy`, the degree formula, is open for every
  `n`, in every characteristic. The missing ingredient in both cases is the theorem of the cube,
  which for a symmetric ample line bundle `L` gives `[n]^* L ≅ L ^ (n ^ 2)`; Mathlib has neither
  the theorem of the cube nor ampleness of line bundles nor intersection numbers. See the
  classical proofs in the individual docstrings. They are owned by issue 776 ("Prove that `[n]`
  is an isogeny of degree `n ^ (2 * g)`: the theorem of the cube and the degree computation").
* TODO: once issue 776 is done, `isFinite_mulBy`, `flat_mulBy` and `surjective_mulBy` subsume
  the `_of_natCast_ne_zero` variants, since `(n : K) ≠ 0` implies `n ≠ 0`; the variants (and
  likewise `exists_npow_eq_of_natCast_ne_zero`, and `isFinite_torsion_of_natCast_ne_zero` and
  `flat_torsion_of_natCast_ne_zero` in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion`) should then be deprecated, so that
  the file is left with a single API.
* Properness of `[n]` is not stated in this file: it is found by instance search, from
  `AlgebraicGeometry.isProper_left`, which says that a morphism in `Over S` whose source is
  proper over `S` and whose target is separated over `S` is proper.
* Naming: a lemma about `[n]` carries the suffix `_of_natCast_ne_zero` exactly when a statement
  of the same conclusion under the weaker hypothesis `n ≠ 0` is also available. So the
  `sorry`-free finiteness, flatness and surjectivity results are suffixed, whereas `etale_mulBy`
  is not: étaleness is false in general when the characteristic of `K` divides `n`, so there is
  no unsuffixed version for it to be confused with.
* Following `WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian`, the dimension `g` of `A`
  is not a field of `IsAbelianVariety` but an instance argument
  `[SmoothOfRelativeDimension g G.hom]` at the use site.

## References

* D. Mumford, *Abelian Varieties*, §6.
* J. S. Milne, *Abelian Varieties*, I.7.

## Blueprint

The declarations of this file implement, in §2.6 of `blueprint/curve_estimates.pdf`:
Proposition 2.7 (`mulBy`, `isFinite_mulBy`, `flat_mulBy`, `surjective_mulBy`, `finrank_mulBy`),
Proposition 2.8 (`etale_mulBy`), Proposition 2.9 (`exists_npow_eq`), and the corollaries for `n`
invertible, `thm:av-mulby-etale-corollaries` (`isFinite_mulBy_of_natCast_ne_zero`,
`flat_mulBy_of_natCast_ne_zero`, `surjective_mulBy_of_natCast_ne_zero`).
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

This is `AlgebraicGeometry.GrpObj.etale_npow_left` specialised to an abelian variety. -/
theorem etale_mulBy (hn : (n : K) ≠ 0) : Etale (mulBy G n).left :=
  GrpObj.etale_npow_left hn

/-- The multiplication by `n` endomorphism of an abelian variety is finite if `n` is invertible
in the base field.

See `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`. -/
theorem isFinite_mulBy_of_natCast_ne_zero (hn : (n : K) ≠ 0) : IsFinite (mulBy G n).left :=
  have := etale_mulBy G hn
  IsFinite.of_isProper_of_locallyQuasiFinite _

/-- The multiplication by `n` endomorphism of an abelian variety is flat if `n` is invertible in
the base field. -/
theorem flat_mulBy_of_natCast_ne_zero (hn : (n : K) ≠ 0) : Flat (mulBy G n).left :=
  have := etale_mulBy G hn
  inferInstance

/-- The multiplication by `n` endomorphism of an abelian variety is surjective if `n` is
invertible in the base field.

See `IsOpenMap.surjective_of_isClosedMap`. -/
theorem surjective_mulBy_of_natCast_ne_zero (hn : (n : K) ≠ 0) : Surjective (mulBy G n).left :=
  have := etale_mulBy G hn
  -- `[n]` is closed, being proper, and open, being flat and locally of finite presentation
  ⟨(mulBy G n).left.isOpenMap.surjective_of_isClosedMap (mulBy G n).left.isClosedMap⟩

section IsAlgClosed

variable [IsAlgClosed K]

/-- **Divisibility of the group of points of an abelian variety.** If `K` is algebraically closed
and `[n]` is finite and surjective, every `K`-point of an abelian variety over `K` is an `n`-th
power; in other words `A(K) / n · A(K) = 0`. -/
theorem exists_npow_eq_of_isFinite_of_surjective [IsFinite (mulBy G n).left]
    [Surjective (mulBy G n).left] (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    ∃ y : 𝟙_ (Over (Spec (.of K))) ⟶ G, y ^ n = x := by
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

/-- **Divisibility of the group of points of an abelian variety.** If `K` is algebraically closed
and `n ≠ 0`, every `K`-point of an abelian variety over `K` is an `n`-th power; in other words
`A(K) / n · A(K) = 0`. -/
theorem exists_npow_eq (hn : n ≠ 0) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    ∃ y : 𝟙_ (Over (Spec (.of K))) ⟶ G, y ^ n = x :=
  have := isFinite_mulBy G hn
  have := surjective_mulBy G hn
  exists_npow_eq_of_isFinite_of_surjective G x

/-- **Divisibility of the group of points of an abelian variety, in good characteristic.** If `K`
is algebraically closed and `n` is invertible in `K`, every `K`-point of an abelian variety over
`K` is an `n`-th power; in other words `A(K) / n · A(K) = 0`. -/
theorem exists_npow_eq_of_natCast_ne_zero (hn : (n : K) ≠ 0)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    ∃ y : 𝟙_ (Over (Spec (.of K))) ⟶ G, y ^ n = x :=
  have := isFinite_mulBy_of_natCast_ne_zero G hn
  have := surjective_mulBy_of_natCast_ne_zero G hn
  exists_npow_eq_of_isFinite_of_surjective G x

/-- The group of `K`-points of an abelian variety over an algebraically closed field `K` is
divisible. -/
noncomputable instance rootableBy : RootableBy (𝟙_ (Over (Spec (.of K))) ⟶ G) ℕ :=
  rootableByOfPowLeftSurj _ _ fun hn x ↦ exists_npow_eq G hn x

end IsAlgClosed

end AlgebraicGeometry.IsAbelianVariety
