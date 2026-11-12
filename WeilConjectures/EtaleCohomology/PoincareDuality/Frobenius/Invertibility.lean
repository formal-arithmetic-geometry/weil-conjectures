/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity

/-!
# Frobenius: invertibility over a coefficient field

Over a coefficient field `Λ`, if the line-valued Poincaré pairing
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d) ≃ Λ` is perfect, the similitude
`⟨F x, F y⟩ = q^d ⟨x, y⟩` with `q^d ≠ 0` forces `F` to be injective on `H^i_c(X, K)`, which is
finite dimensional, hence `F` is invertible there. This is a clause of blueprint
`theorem-poincare-duality-frobenius`.

## Main statements

- `LinearMap.isUnit_of_similitude_of_isField`: the first member of a similitude pair for a
  perfect pairing over a field is invertible.
- `AlgebraicGeometry.Etale.TateOrientation.isUnit_frobeniusOperator_lowerShriek`: `F` is
  invertible on `H^i_c(X, K)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace LinearMap

variable {L V W : Type*} [CommRing L] [AddCommGroup V] [Module L V] [AddCommGroup W]
  [Module L W] {p : V →ₗ[L] W →ₗ[L] L} [p.IsPerfPair] {F : Module.End L V}
  {G : Module.End L W} {c : L}

/-- Over a commutative ring `L` that is a field, the first member `F` of a similitude pair
`p (F v) (G w) = c * p v w`, `c ≠ 0`, for a perfect pairing `p` is invertible: it is injective
(`LinearMap.injective_of_similitude`) and `V` is finite dimensional, being reflexive. -/
theorem isUnit_of_similitude_of_isField (hL : IsField L) (hc : c ≠ 0)
    (hFG : ∀ v w, p (F v) (G w) = c * p v w) : IsUnit F := by
  let := hL.toField
  have := Module.IsReflexive.of_isPerfPair p
  have hinj := injective_of_similitude hc hFG
  exact (Module.End.isUnit_iff F).2 ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end LinearMap

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- Blueprint `theorem-poincare-duality-frobenius--5`: invertibility over a coefficient field.

If `Λ` is a field, then with the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`
(a Weil complex `(K, φ)` with the contragredient structure `ψ` on `K^∨`, the Frobenius `τ`
acting by `q^d` on the value line `Λ(-d)`, `q` invertible in `Λ`, and the line-valued pairing
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d) ≃ Λ` perfect), the Frobenius operator `F` is invertible
on `H^i_c(X, K)`. -/
theorem isUnit_frobeniusOperator_lowerShriek (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z) (hΛ : IsField Λ)
    (hq : (q : Λ) ≠ 0) (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y (-d)) ≃ₗ[Λ] Λ)
    [((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).IsPerfPair] :
    IsUnit (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)) :=
  LinearMap.isUnit_of_similitude_of_isField
    (p := (γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap)
    (G := frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j))
    (c := (q : Λ) ^ d) hΛ
    (by have := hΛ.isDomain; exact pow_ne_zero _ hq) (fun x y ↦ by
      rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply,
        untwistedDegreewisePoincarePairing_frobeniusOperator sq γ φ ψ hψ τ hTr q hτ, map_smul,
        smul_eq_mul])

end TateOrientation

end Etale

end AlgebraicGeometry
