/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# Strict Weil data and the Tate datum

Let `f : X ⟶ Y` be the base change to `k̄` of a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite
field, smooth of relative dimension `d`, and let `g_X`, `g_Y` be the geometric-Frobenius
automorphisms of `X` and `Y`, which form a cartesian square `g_X ≫ f = f ≫ g_Y`
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`). Following
blueprint `def-pur-tate-datum`, a *strict geometric-Weil datum* on `K ∈ D(Y_ét, Λ)` is an
isomorphism `φ_K : Lg_Y^* K ≅ K`, a Weil structure in the sense of `sk-def-sf-weil-complexes`
(`AlgebraicGeometry.Etale.WeilComplex`). This file constructs the Weil data that the smooth purity
chapter transports through the purity isomorphism:

* the *Tate datum* `τ_r : Lg^* Λ_Y(r) ≅ Λ_Y(r)` of the Tate twist
  (`AlgebraicGeometry.Etale.tateWeilDatum`): the identification of the twist datum with its
  pullback along `g`;
* the datum `φ^pur_{f,K}` on the source `Lf^* K(d)[2d]` of smooth purity
  (`AlgebraicGeometry.Etale.smoothPurityWeilDatum`): the base change identification followed by
  `Lf^* φ_K`, the Tate datum `τ_d` entering through the base change identification;
* the datum `φ^!_{f,K}` on the exceptional inverse image `Rf^! K`
  (`AlgebraicGeometry.Etale.upperShriekWeilDatum`): the smooth pullback exchange
  `Ex^{!,sm}_{f,g_Y,K}` of `def-pur-smooth-pullback-exchange` followed by `Rf^!(φ_K)`.

The scheme-Frobenius form `u_K = φ_K ∘ κ_{Y,K}` of a datum is
`AlgebraicGeometry.Etale.schemeFrobeniusForm` in
`WeilConjectures.EtaleCohomology.Purity.Smooth.SchemeFrobeniusForm`.

## Implementation notes

The constructions only use the commutativity of the squares (and their cartesianness for the
smooth pullback exchange), so they are stated for arbitrary endomorphisms `g_X`, `g_Y` forming
such a square; the geometric-Frobenius automorphisms are the case of interest. As for
`AlgebraicGeometry.Etale.smoothPullbackExchange`, the identifications `θ` of the dualizing complex
and the tensor formulas `φ` are arguments of the construction of `φ^!_{f,K}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Tate

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]

/-- Blueprint `def-pur-tate-datum`: Strict Weil data and the Tate datum.

The *Tate datum* `τ_r : Lg^* Λ_X(r) ≅ Λ_X(r)` on the Tate twist `Λ_X(r)` for an endomorphism
`g` of `X` (for `g = g_{X,γ}` the geometric-Frobenius automorphism): the identification
`Lg^* Λ_X(r) ≅ Λ_X(r)` of the Tate twist datum
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTateObjectIso`). This is the canonical Weil
structure of the twist, the twist normalization of `def-weil-frobenius-coefficient-twists`,
on which geometric Frobenius acts by `q^{-r}`. -/
noncomputable def tateWeilDatum (g : X ⟶ X) (r : ℤ) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X r) ≅ tateObject Λ X r :=
  leftDerivedUpperStarTateObjectIso g r

end Tate

section Purity

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [HasInvertibleExponent Λ X] {gX : X ⟶ X} {gY : Y ⟶ Y}

variable (d) in
/-- Blueprint `def-pur-tate-datum`: Strict Weil data and the Tate datum.

The datum `φ^pur_{f,K}` induced on the source `Lf^* K(d)[2d]` of smooth purity by a strict Weil
datum `φ_K : Lg_Y^* K ≅ K`, for a commutative square `g_X ≫ f = f ≫ g_Y`:
```
                          ≅                                   Lf^* φ_K ⊗ τ_d
  Lg_X^*(Lf^* K(d)[2d]) ────▶ Lf^* Lg_Y^* K ⊗ Lg_X^* Λ_X(d)[2d] ──────────────▶ Lf^* K(d)[2d].
```
The first arrow moves `Lg_X^*` through the twist and shift and identifies
`Lg_X^* Lf^* ≅ Lf^* Lg_Y^*` along the square, the Tate datum `τ_d` of `Λ_X(d)`
(`AlgebraicGeometry.Etale.tateWeilDatum`) being applied on the twisting factor
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftBaseChangeIso`); the second applies
`Lf^* φ_K`. -/
noncomputable def smoothPurityWeilDatum (sq : CommSq gX f f gY)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq K ≪≫
    (twistShift Λ X d).mapIso ((L((f)^*[ModuleCat.{u + 1} Λ])).mapIso φ)

/-- Blueprint `def-pur-tate-datum`: Strict Weil data and the Tate datum.

The datum `φ^!_{f,K}` induced on the exceptional inverse image `Rf^! K` by a strict Weil datum
`φ_K : Lg_Y^* K ≅ K`, for a cartesian square `g_X ≫ f = f ≫ g_Y`:
```
                Ex^{!,sm}_{f,g_Y,K}                 Rf^!(φ_K)
  Lg_X^* Rf^! K ───────────────────▶ Rf^! Lg_Y^* K ──────────▶ Rf^! K,
```
the smooth pullback exchange of `def-pur-smooth-pullback-exchange`
(`AlgebraicGeometry.Etale.smoothPullbackExchange`) followed by `Rf^!(φ_K)`. The identifications
`θ : ω_f ≅ Λ_X(d)[2d]` and the tensor formulas `φf : Lf^* K ⊗ ω_f ≅ Rf^! K`,
`φf' : Lf^* Lg_Y^* K ⊗ ω_f ≅ Rf^! Lg_Y^* K` that the exchange is built from are arguments. -/
noncomputable def upperShriekWeilDatum (sq : IsPullback gX f f gY)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K)
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φf : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K)
    (φf' : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  smoothPullbackExchange Λ f sq K θ φf θ φf' ≪≫
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso φ

omit [IsSeparated f] [SmoothOfRelativeDimension d f] in
/-- The datum `φ^!_{f,K}` corresponds to the datum `φ^pur_{f,K}` under the smooth purity
isomorphism `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K` (`AlgebraicGeometry.Etale.smoothPurityIso`) built
from `θ` and `φf`, provided the purity isomorphism of `Lg_Y^* K` built from `θ` and `φf'` is
compatible with `φ_K` (that is, `γ_{f,-}` is natural along `φ_K`): `γ_{f,K}` is then a morphism
of Weil objects. -/
theorem smoothPurityIso_hom_comp_upperShriekWeilDatum (sq : IsPullback gX f f gY)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K)
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φf : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K)
    (φf' : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K))
    (hφ : (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ.hom) ≫
        (smoothPurityIso Λ f K θ φf).hom =
      (smoothPurityIso Λ f _ θ φf').hom ≫ (rightDerivedUpperShriek _ f).map φ.hom) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).map (smoothPurityIso Λ f K θ φf).hom ≫
        (upperShriekWeilDatum Λ f sq φ θ φf φf').hom =
      (smoothPurityWeilDatum Λ d f sq.toCommSq φ).hom ≫ (smoothPurityIso Λ f K θ φf).hom := by
  rw [upperShriekWeilDatum, Iso.trans_hom, reassoc_of%
    leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom Λ f sq K θ φf θ φf',
    smoothPurityWeilDatum, Iso.trans_hom, Category.assoc, Functor.mapIso_hom]
  exact congrArg (_ ≫ ·) hφ.symm

end Purity

end Etale

end AlgebraicGeometry
