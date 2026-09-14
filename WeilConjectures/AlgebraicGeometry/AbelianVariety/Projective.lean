/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Symmetric
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Projectivity of an abelian variety, and a symmetric ample line bundle

An abelian variety `G` over a field `K` is projective: the scheme `G.left` carries an ample line
bundle, equivalently it admits a closed immersion over `K` into a projective space over `K`.
This is the one input of the degree chapter that is specific to abelian varieties, and it is
stated here without proof.

Granting it, `G.left` carries an ample line bundle which is moreover *symmetric* in the sense of
`AlgebraicGeometry.Scheme.Modules.IsSymmetric`, that is, fixed by pullback along the inversion
`ι` of `G`. Indeed, if `L₀` is ample then so is `ι^* L₀`, since `ι` is an isomorphism, hence so
is `L := L₀ ⊗ ι^* L₀`; and `L` is symmetric by
`AlgebraicGeometry.Scheme.Modules.isSymmetric_tensorObj_pullback`. A symmetric ample line bundle
is what the theorem of the cube is applied to in order to compute the degree of the isogeny
`[n]`.

Throughout, a group scheme is an object `G : Over (Spec (.of K))` carrying a
`CategoryTheory.GrpObj G` structure, as in
`WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian`: its underlying scheme is `G.left`,
and its inversion `[-1]` is `ι[G]`, the two being equal by
`CategoryTheory.GrpObj.zpow_neg_one`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple` — an abelian variety carries an
  ample line bundle (blueprint: `prop:deg-abelian-projective`).
- `AlgebraicGeometry.IsAbelianVariety.exists_isClosedImmersion` — **an abelian variety is
  projective**: it admits a closed immersion over `K` into a projective space over `K`
  (blueprint: `prop:deg-abelian-projective`).
- `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple_isSymmetric` — **an abelian
  variety carries a symmetric ample line bundle** (blueprint: `prop:deg-symmetric-ample`).

## Implementation notes

* `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple` is an open obligation of the
  degree chapter: it is stated and left `sorry`, exactly as
  `WeilConjectures.AlgebraicGeometry.ChowLemma` states Chow's lemma without proving it. The
  other two statements are proved from it, and inherit its `sorry`.

* **Generality.** The blueprint chapter works throughout over an algebraically closed field.
  Nothing in the statements below needs that, and neither does the classical proof of
  projectivity, so all are stated over an arbitrary field `K`; a consumer working over an
  algebraically closed field can use them unchanged.

## TODO

* Prove `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple`, following Mumford,
  *Abelian Varieties*, §6. Choose an affine open `U ⊆ G.left` containing the identity. Since
  `G.left` is smooth and the complement of an affine open in a smooth variety is of pure
  codimension one, the reduced complement `D := G.left \ U` is an effective divisor with
  `G.left \ Supp D = U` affine; one then shows that `𝒪(3 D)` is very ample, translating `D` by
  the theorem of the square to separate any pair of points and any tangent vector. The argument
  uses only the group law and the affineness of `U`, not the theorem of the cube, which is why
  it belongs to the degree chapter.

## References

* D. Mumford, *Abelian Varieties*, §6.
* J. S. Milne, *Abelian Varieties*, I §7.

## Blueprint

This file states `prop:deg-abelian-projective` and proves `prop:deg-symmetric-ample` of
`curve_estimates/28_degree_of_the_isogeny.tex`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.IsAbelianVariety

open CategoryTheory MonoidalCategory Scheme.Modules

open scoped MonObj

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] [IsAbelianVariety G]

/-- **An abelian variety carries an ample line bundle**, that is, it is projective.

The classical proof is Mumford, *Abelian Varieties*, §6: the complement of an affine open
neighbourhood `U` of the identity is an effective divisor `D`, and `𝒪(3 D)` is very ample by
the theorem of the square.
(blueprint: `prop:deg-abelian-projective`) -/
theorem exists_invertible_isAmple :
    ∃ L : G.left.Modules, L.Invertible ∧ L.IsAmple :=
  sorry

/-- **An abelian variety is projective**: it admits a closed immersion over `K` into a
projective space over `K`, namely the one cut out by a power of an ample line bundle on it.
(blueprint: `prop:deg-abelian-projective`) -/
theorem exists_isClosedImmersion :
    ∃ (N : ℕ) (i : G.left ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of K))),
      IsClosedImmersion i ∧ i.IsOver (Spec (.of K)) := by
  obtain ⟨L, hL, hLa⟩ := exists_invertible_isAmple G
  obtain ⟨_, N, _, i, hi, hio, _⟩ := hLa.exists_isClosedImmersion K hL
  exact ⟨N, i, hi, hio⟩

/-- **An abelian variety carries a symmetric ample line bundle.**
(blueprint: `prop:deg-symmetric-ample`) -/
theorem exists_invertible_isAmple_isSymmetric :
    ∃ L : G.left.Modules, L.Invertible ∧ L.IsAmple ∧ L.IsSymmetric G := by
  obtain ⟨L₀, hL₀, hL₀a⟩ := exists_invertible_isAmple G
  -- `L₀ ⊗ ι^* L₀` is ample as a tensor product of ample line bundles, `ι` being an isomorphism,
  -- and symmetric because `ι ≫ ι = 𝟙`.
  exact ⟨L₀ ⊗ (pullback ι[G].left).obj L₀, hL₀.tensorObj (hL₀.pullback _),
    IsAmple.tensorObj hL₀ (hL₀.pullback _) hL₀a (hL₀a.pullback_of_isIso _),
    isSymmetric_tensorObj_pullback G L₀⟩

end AlgebraicGeometry.IsAbelianVariety
