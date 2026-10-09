/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.ZetaLinearAlgebra.Pairing

/-!
# Frobenius: equivariance, similitude, reciprocity

Let `a : X ⟶ Y` admit a compactification, `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` be a Tate orientation and
`g : X ⟶ X`, `h : Y ⟶ Y` with `g ≫ a = a ≫ h` (cartesian). In the setting of the Poincaré
duality chapter `Y = Spec k`, `X = X₀ ×_{k₀} k` and `g`, `h` are the geometric Frobenius
automorphisms. A strict Weil complex `(K, φ)` on `X` gives Weil data on `RΓ_c(X, K) = Ra_! K`
and on `RΓ(X, M) = Ra_* M`, whose Frobenius operators are the geometric Frobenius `F_{c,K}` on
`H^i_c(X, K)` and `F_M` on `H^j(X, M)`. This file proves the Frobenius statements of
`sk-thm-frobenius`.

**(a) Equivariance and similitude.** The derived Poincaré pairing `β_K` is a morphism of Weil
objects, so the degreewise pairing
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` satisfies `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i =
⟨x, y⟩_i`, and the untwisted, line-valued pairing
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)` satisfies
`⟨F_{c,K} x, F_{K^∨} y⟩^{untw}_i = q^d ⟨x, y⟩^{untw}_i`.

**(b) Reciprocity.** Over a field, if the line-valued pairing is perfect, `F_{K^∨}` is
conjugate to `q^d (F_{c,K}^{-1})^t`, so the eigenvalues of `F` on `H^{2d-i}(X, K^∨)` are the
`q^d / α` for the eigenvalues `α` of `F` on `H^i_c(X, K)`, with multiplicities.

## Main definitions

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`
  (`prop-pod-degree-of-the-pairing`): `⟨-, -⟩_i`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing`
  (`prop-pod-degree-of-the-pairing`): the untwisted pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` and its degreewise form.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator`
  (`sk-thm-frobenius` (a)): `β_K` is a morphism of Weil objects, and the degreewise pairing is
  Frobenius invariant.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`
  (`cor-pod-untwisted-similitude`): the untwisted similitude with factor `q^d`.
- `AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`,
  `AlgebraicGeometry.Etale.TateOrientation.roots_map_charpoly_frobeniusOperator`
  (`cor-pod-reciprocal-eigenvalues`, `sk-thm-frobenius` (b)): conjugacy and reciprocal
  eigenvalues.

## Implementation notes

The Tate twist `Λ(d)` is a datum (`AlgebraicGeometry.Etale.HasTateTwist`) and the orientation
`γ` is arbitrary, so the Frobenius structures on the twists and the Frobenius equivariance of
the smooth trace (`thm-pur-weil-equivariance-of-purity-and-trace`) are hypotheses: a Weil datum
`τ` on `Λ_X(d)` for which the smooth trace is a morphism of Weil objects, and a Weil datum on
`Λ_Y(-d)` on whose sections Frobenius acts by `q^d`
(`def-weil-frobenius-coefficient-twists`). The contragredient datum on `K^∨` (resp. `K^∨(d)`) is
characterised by the Frobenius equivariance of the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` (resp. of the
twisted evaluation `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`), which determines it when `K` is dualizable.

The second factor `H^{2d-i}(X, K^∨(d))` is read as `Hom(Λ_Y, (Ra_* K^∨(d))[j])` with
`i + j = 2d`, and the degreewise pairing passes through
`(Ra_* K^∨(d))[j] ≅ ((Ra_* K^∨(d))[2d])[j - 2d]`, the shift convention of
`prop-pod-degree-of-the-pairing`.

The reciprocity statement assumes the line-valued pairing perfect after a trivialisation
`Hom(Λ_Y, Λ_Y(-d)) ≃ Λ` of the value line; at a field stage this is
`thm-pod-degreewise-perfectness-over-a-field`. Over `𝒪_E` it fails (the blueprint's example
`K = [𝒪_E --ϖ--> 𝒪_E]` over a point), which is why (b) is stated over a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

/-- Blueprint `sk-thm-frobenius`: Frobenius: equivariance, similitudine, reciprocity (a).

**The derived Poincaré pairing of a purity isomorphism is a morphism of Weil objects**: the
form of `AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing` for a purity
isomorphism `γ : T[2d] ≅ ω_X`, a Weil datum `τ` on `T`, and the pairing
`AlgebraicGeometry.Etale.poincarePairing`. -/
theorem isWeilPairing_poincarePairing (sq : IsPullback g a a h)
    {T : DerivedCategoryModule Λ X}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor _ X).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T) ⟶
      ((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation T K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom (smoothTrace γ)) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) (2 * d))
      (leftDerivedUpperStarUnitIso _ h).hom (poincarePairing a γ K) := by
  have h1 := ((isWeilPairing_mixedSupportCupProduct sq φ ψ).comp
    (hψ.rightDerivedLowerShriek_map sq)).shift_right (2 * d)
  refine ((h1.comp (isWeilMorphism_rightDerivedLowerShriek_commShiftIso_inv sq τ
    (2 * d))).comp hTr).of_eq ?_
  simp only [poincarePairing, poincarePairingEvaluation, Category.assoc]

/-- **The pairing of a Frobenius-equivariant trace is a morphism of Weil objects.** Let `φ` be a
Weil datum on `K`, `ψ` the contragredient datum on `K^∨`, characterised by the Frobenius
equivariance of the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`, and `t : (Ra_! Λ_X)[n] ⟶ T` a morphism of Weil
objects for a Weil datum `τ` on `T`. Then the pairing of `t`
(`AlgebraicGeometry.Etale.poincarePairingOfTrace`) is a morphism of Weil objects for the data
`φ_{c,K}`, `φ_{K^∨}[n]` and `τ`. -/
theorem isWeilPairing_poincarePairingOfTrace (sq : IsPullback g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K)) {T : DerivedCategoryModule Λ Y} (n : ℤ)
    (t : ((R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))⟦n⟧ ⟶ T)
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T)
    (ht : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) n) τ t) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) n) τ
      (poincarePairingOfTrace a K n t) :=
  (((isWeilPairing_mixedSupportCupProduct sq φ ψ).comp
    (hψ.rightDerivedLowerShriek_map sq)).shift_right n).comp ht

end Generic

namespace TateOrientation

section Pairings

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] {d : ℕ}

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The *degreewise Poincaré pairing* of a Tate orientation `γ`, for `i + j = 2d`,

`⟨-, -⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`,

with `H^i_c(X, K) = Hom(Λ_Y, (Ra_! K)[i])`, `H^j(X, K^∨(d)) = Hom(Λ_Y, (Ra_* K^∨(d))[j])` and
`Λ = End(Λ_Y)` (for `Y = Spec k`): the degreewise pairing
(`AlgebraicGeometry.Etale.degreewisePairing`) of the derived Poincaré pairing `β_K` in degrees
`i` and `j - 2d`, read through `(Ra_* K^∨(d))[j] ≅ ((Ra_* K^∨(d))[2d])[j - 2d]` and
`Λ_Y[i + (j - 2d)] ≅ Λ_Y`. -/
noncomputable def degreewisePoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) →ₗ[Λ]
          (𝟙_ (DerivedCategoryModule Λ Y) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  ((degreewisePairing (γ.poincarePairing K) i (j - 2 * d)).compl₂
    (Linear.rightComp Λ _ ((shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
      (by omega)).hom.app _))).compr₂
    (Linear.rightComp Λ _ ((shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d))
      (by omega)).hom.app _))

lemma degreewisePoincarePairing_apply (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij x y =
      degreewisePairing (γ.poincarePairing K) i (j - 2 * d) x
          (y ≫ (shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
            (by omega)).hom.app _) ≫
        (shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d)) (by omega)).hom.app _ :=
  rfl

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The *untwisted derived Poincaré pairing* of a Tate orientation `γ`,

`β_K^{untw} : Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨)[2d] ⟶ Λ(-d)`: the shift is moved out, then come the
mixed-support cup product, `Ra_!` of the evaluation `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` and the untwisted
smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)`
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`), which eliminates the twist
`Λ_X(d)` of `β_K` through `Λ_Y(d) ⊗ᴸ Λ_Y(-d) ≅ Λ_Y`; this is
`AlgebraicGeometry.Etale.poincarePairingOfTrace` for the untwisted smooth trace. -/
noncomputable def untwistedPoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦(2 * d : ℤ)⟧) ⟶
      tateObject Λ Y (-d) :=
  poincarePairingOfTrace a K (2 * d : ℤ) γ.untwistedSmoothTrace

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The *untwisted degreewise Poincaré pairing* of a Tate orientation `γ`, for `i + j = 2d`, the
line-valued pairing

`⟨-, -⟩^{untw}_i : H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`,

with `Λ(-d) = Hom(Λ_Y, Λ_Y(-d))` for `Y = Spec k`: the degreewise pairing of the untwisted
derived pairing (`AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`), read as
in `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`. -/
noncomputable def untwistedDegreewisePoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →ₗ[Λ]
          (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y (-d)) :=
  ((degreewisePairing (γ.untwistedPoincarePairing K) i (j - 2 * d)).compl₂
    (Linear.rightComp Λ _ ((shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
      (by omega)).hom.app _))).compr₂
    (Linear.rightComp Λ _ ((shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d))
      (by omega)).hom.app _))

lemma untwistedDegreewisePoincarePairing_apply (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) :
    γ.untwistedDegreewisePoincarePairing K i j hij x y =
      degreewisePairing (γ.untwistedPoincarePairing K) i (j - 2 * d) x
          (y ≫ (shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
            (by omega)).hom.app _) ≫
        (shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d)) (by omega)).hom.app _ :=
  rfl

end Pairings

section Equivariance

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

/-- Blueprint `sk-thm-frobenius`: Frobenius: equivariance, similitudine, reciprocity (a).

**The derived Poincaré pairing is a morphism of Weil objects.** Let `φ` be a Weil datum on `K`,
`τ` one on `Λ_X(d)` for which the smooth trace `Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y` is a morphism of Weil
objects (the trace square of `thm-pur-weil-equivariance-of-purity-and-trace`, the target
carrying the canonical datum), and `ψ` the contragredient datum on `K^∨(d)`, characterised by
the Frobenius equivariance of the twisted evaluation `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`. Then

`β_K : Ra_! K ⊗ᴸ (Ra_* K^∨(d))[2d] ⟶ Λ_Y`

is a morphism of Weil objects, for the data `φ_{c,K}`, `φ_{K^∨(d)}[2d]` and the canonical datum
of `Λ_Y`. -/
theorem isWeilPairing_poincarePairing (sq : IsPullback g a a h) (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K) ⟶ twistedDual Λ d K)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation (tateObject Λ X d) K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) (2 * d))
      (leftDerivedUpperStarUnitIso _ h).hom (γ.poincarePairing K) :=
  Etale.isWeilPairing_poincarePairing sq γ.dualizingComplexIso φ τ ψ hψ hTr

/-- Blueprint `sk-thm-frobenius`: Frobenius: equivariance, similitudine, reciprocity (a).

**Frobenius equivariance of the degreewise pairing**, in the form
`⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = F(⟨x, y⟩_i)` with `F` the Frobenius of the canonical datum on
`Λ = End(Λ_Y)` (see
`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator_eq` for the
form `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`). The hypotheses are those of
`AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing`; no nondegeneracy is
used. -/
theorem degreewisePoincarePairing_frobeniusOperator (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K) ⟶ twistedDual Λ d K)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation (tateObject Λ X d) K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j) y) =
      frobeniusOperator h (leftDerivedUpperStarUnitIso _ h).hom
        (γ.degreewisePoincarePairing K i j hij x y) := by
  rw [degreewisePoincarePairing_apply, degreewisePoincarePairing_apply,
    ← frobeniusOperator_shiftWeilDatum_comp_shiftFunctorAdd',
    (isWeilPairing_poincarePairing sq γ φ τ ψ hψ hTr).degreewisePairing_frobeniusOperator,
    frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero']

/-- Blueprint `sk-thm-frobenius`: Frobenius: equivariance, similitudine, reciprocity (a).

**Frobenius invariance of the degreewise pairing**: `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`,
when every endomorphism of `Λ_Y` is a scalar (as for `Y = Spec k`, `k` separably closed), so
that geometric Frobenius acts trivially on the value ring `Λ`. -/
theorem degreewisePoincarePairing_frobeniusOperator_eq (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K) ⟶ twistedDual Λ d K)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation (tateObject Λ X d) K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace)
    (hY : ∀ v : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ 𝟙_ _, ∃ c : Λ, v = c • 𝟙 _)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j) y) =
      γ.degreewisePoincarePairing K i j hij x y := by
  rw [degreewisePoincarePairing_frobeniusOperator sq γ φ τ ψ hψ hTr,
    frobeniusOperator_unit_eq_self h hY]

/-- Blueprint `sk-thm-frobenius`: Frobenius: equivariance, similitudine, reciprocity (a).

**The untwisted derived Poincaré pairing is a morphism of Weil objects.** Let `φ` be a Weil
datum on `K`, `ψ` the contragredient datum on `K^∨`, characterised by the Frobenius equivariance
of the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` (the target carrying the canonical datum), and `τ` a Weil
datum on `Λ_Y(-d)` for which the untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)` is a
morphism of Weil objects. Then `β_K^{untw} : Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` is a morphism
of Weil objects for the data `φ_{c,K}`, `φ_{K^∨}[2d]` and `τ`. -/
theorem isWeilPairing_untwistedPoincarePairing (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) (2 * d)) τ
      (γ.untwistedPoincarePairing K) :=
  isWeilPairing_poincarePairingOfTrace sq φ ψ hψ (2 * d) _ τ hTr

/-- Blueprint `cor-pod-untwisted-similitude`: Untwisted similitude.

**The untwisted similitude.** With the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_untwistedPoincarePairing`, and if
geometric Frobenius acts on the value line `Λ(-d) = Hom(Λ_Y, Λ_Y(-d))` by `q^d` (the
normalisation `def-weil-frobenius-coefficient-twists` of the datum `τ`), then for
`x ∈ H^i_c(X, K)` and `y ∈ H^{2d-i}(X, K^∨)`

`⟨F_{c,K} x, F_{K^∨} y⟩^{untw}_i = q^d ⟨x, y⟩^{untw}_i`.

These are identities of bilinear maps; no nondegeneracy is used. -/
theorem untwistedDegreewisePoincarePairing_frobeniusOperator (sq : IsPullback g a a h)
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
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) :
    γ.untwistedDegreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j) y) =
      ((q : Λ) ^ d) • γ.untwistedDegreewisePoincarePairing K i j hij x y := by
  rw [untwistedDegreewisePoincarePairing_apply, untwistedDegreewisePoincarePairing_apply,
    ← frobeniusOperator_shiftWeilDatum_comp_shiftFunctorAdd',
    (isWeilPairing_untwistedPoincarePairing sq γ φ ψ hψ τ hTr).degreewisePairing_frobeniusOperator,
    frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero', hτ]

/-- Blueprint `cor-pod-untwisted-similitude`: Untwisted similitude.

**The untwisted similitude for the constant complex.** Let `K = Λ_X` with its canonical datum,
`ψ` the contragredient datum on `Λ_X^∨`, and `ι : Λ_X ⟶ Λ_X^∨` a morphism of Weil objects from
the canonical datum to `ψ` (the canonical identification `Λ_X^∨ ≅ Λ_X`). Then for
`x ∈ H^i_c(X, Λ)` and `y ∈ H^{2d-i}(X, Λ)`, with `F` the geometric Frobenius of the canonical
datum on both, the pairing `⟨x, y⟩ = ⟨x, ι_* y⟩^{untw}_i` satisfies
`⟨F x, F y⟩ = q^d ⟨x, y⟩`. -/
theorem untwistedDegreewisePoincarePairing_unit_frobeniusOperator (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X)))) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X))))
    (hψ : IsWeilPairing g (leftDerivedUpperStarUnitIso _ g).hom ψ
      (leftDerivedUpperStarUnitIso _ g).hom (DerivedCategory.coefficientEvaluation _))
    (ι : 𝟙_ (DerivedCategoryModule Λ X) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X))))
    (hι : IsWeilMorphism g (leftDerivedUpperStarUnitIso _ g).hom ψ ι)
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ X)))⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ X)))⟦j⟧) :
    γ.untwistedDegreewisePoincarePairing _ i j hij
        (frobeniusOperator h (shiftWeilDatum h
          (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) i) x)
        (frobeniusOperator h (shiftWeilDatum h
            (lowerStarWeilDatum sq.toCommSq (leftDerivedUpperStarUnitIso _ g).hom) j) y ≫
          ((R((a)_*[ModuleCat.{u + 1} Λ])).map ι)⟦j⟧') =
      ((q : Λ) ^ d) • γ.untwistedDegreewisePoincarePairing _ i j hij x
        (y ≫ ((R((a)_*[ModuleCat.{u + 1} Λ])).map ι)⟦j⟧') := by
  rw [← ((hι.rightDerivedLowerStar_map sq.toCommSq).shift j).frobeniusOperator_comp,
    untwistedDegreewisePoincarePairing_frobeniusOperator sq γ _ ψ hψ τ hTr q hτ]

end Equivariance


section Reciprocity

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

/-- Blueprint `cor-pod-reciprocal-eigenvalues`: Reciprocal eigenvalues.

**The Frobenius of the dual is conjugate to `q^d` times the inverse transpose.** If `Λ` is a
field, then with the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`,
`q` invertible in `Λ`, and the line-valued pairing
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d) ≃ Λ` perfect (for a trivialisation `ℓ` of the value
line; at a field stage this is `thm-pod-degreewise-perfectness-over-a-field`), the adjoint
`Φ : H^{2d-i}(X, K^∨) ≃ H^i_c(X, K)^∨` of the pairing satisfies

`Φ ∘ F_{K^∨} ∘ Φ⁻¹ = q^d (F_{c,K}^{-1})^t`.

In particular `F_{c,K}` is invertible (`Ring.inverse` is its inverse transpose). -/
theorem conj_frobeniusOperator_eq_smul_inverse_dualMap (sq : IsPullback g a a h)
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
    ((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).flip.toPerfPair.conj
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j)) =
      ((q : Λ) ^ d) •
        Ring.inverse
          (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)).dualMap := by
  refine LinearMap.conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude_of_isField hΛ
    (by have := hΛ.isDomain; exact pow_ne_zero _ hq) fun x y ↦ ?_
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply,
    untwistedDegreewisePoincarePairing_frobeniusOperator sq γ φ ψ hψ τ hTr q hτ, map_smul,
    smul_eq_mul]

/-- Blueprint `cor-pod-reciprocal-eigenvalues`: Reciprocal eigenvalues.

**Reciprocal eigenvalues.** With the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`, the
eigenvalues of `F_{K^∨}` on `H^{2d-i}(X, K^∨)`, computed in an algebraically closed field `M`
containing `Λ` and counted with algebraic multiplicity, are the `q^d / α` for the eigenvalues
`α` of `F_{c,K}` on `H^i_c(X, K)`. The finiteness and freeness of the two spaces, needed to
speak of characteristic polynomials, also follow from the perfectness of the pairing over the
field `Λ`. -/
theorem roots_map_charpoly_frobeniusOperator (sq : IsPullback g a a h)
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
    [((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).IsPerfPair]
    [Module.Free Λ
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)]
    [Module.Finite Λ
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)]
    [Module.Free Λ (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧)]
    [Module.Finite Λ (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧)]
    {M : Type*} [Field M] [IsAlgClosed M] (ι : Λ →+* M) :
    ((frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j)).charpoly.map
        ι).roots =
      ((frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)).charpoly.map
        ι).roots.map fun z ↦ ι ((q : Λ) ^ d) / z :=
  LinearMap.roots_map_charpoly_of_similitude_of_isField
    (p := (γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap) hΛ
    (by have := hΛ.isDomain; exact pow_ne_zero _ hq) (fun x y ↦ by
      rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply,
        untwistedDegreewisePoincarePairing_frobeniusOperator sq γ φ ψ hψ τ hTr q hτ, map_smul,
        smul_eq_mul]) ι

end Reciprocity

end TateOrientation

end Etale

end AlgebraicGeometry
