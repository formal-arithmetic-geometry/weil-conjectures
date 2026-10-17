/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UntwistedPerfectness

/-!
# Frobenius: reciprocity

Part (b) of `sk-thm-frobenius`. Over a field, if the line-valued Poincaré pairing is perfect,
`F_{K^∨}` is conjugate to `q^d (F_{c,K}^{-1})^t`, so the eigenvalues of `F` on
`H^{2d-i}(X, K^∨)` are the `q^d / α` for the eigenvalues `α` of `F` on `H^i_c(X, K)`, with
multiplicities.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`,
  `AlgebraicGeometry.Etale.TateOrientation.roots_map_charpoly_frobeniusOperator`
  (`cor-pod-reciprocal-eigenvalues`, `sk-thm-frobenius` (b)): conjugacy and reciprocal
  eigenvalues.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace TateOrientation

section Reciprocity

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

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

section FiniteField

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [Finite Λ] [HasTateTwist Λ] {k : Type u}
  [Field k] [IsSepClosed k] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [QuasiCompact a] [LocallyOfFiniteType a] {d : ℕ} {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `cor-pod-reciprocal-eigenvalues`: Reciprocal eigenvalues (finite-field stage).

**The Frobenius of the dual is conjugate to `q^d` times the inverse transpose.** At a finite
field stage `Λ` (a finite domain), over a separably closed field `k`, for `K ∈ D^b_{ctf}(X, Λ)`
and with the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap` other
than the perfectness of the line-valued pairing, which holds here
(`AlgebraicGeometry.Etale.TateOrientation.isPerfPair_untwistedDegreewisePoincarePairing`,
blueprint `thm-pod-degreewise-perfectness-over-a-field`): the adjoint
`Φ : H^{2d-i}(X, K^∨) ≃ H^i_c(X, K)^∨` of the line-valued pairing satisfies
`Φ ∘ F_{K^∨} ∘ Φ⁻¹ = q^d (F_{c,K}^{-1})^t`. -/
theorem conj_frobeniusOperator_eq_smul_inverse_dualMap_of_isSepClosed (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ (Spec (.of k)) (-d)) ⟶
      tateObject Λ (Spec (.of k)) (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z)
    (hq : (q : Λ) ≠ 0) (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ (Spec (.of k)) (-d)) ≃ₗ[Λ]
      Λ) :
    letI := γ.isPerfPair_untwistedDegreewisePoincarePairing hK i j hij ℓ
    ((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).flip.toPerfPair.conj
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j)) =
      ((q : Λ) ^ d) •
        Ring.inverse
          (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)).dualMap :=
  letI := γ.isPerfPair_untwistedDegreewisePoincarePairing hK i j hij ℓ
  conj_frobeniusOperator_eq_smul_inverse_dualMap sq γ φ ψ hψ τ hTr q hτ
    (Finite.isField_of_domain Λ) hq i j hij ℓ

omit [HasTateTwist Λ] [QuasiCompact a] in
/-- At a finite field stage, over a separably closed field, `H^i_c(X, K) = Hom(Λ_s, (Ra_! K)[i])`
is a finite free `Λ`-module for `K ∈ D^b_{ctf}(X, Λ)`. -/
lemma free_and_finite_hom_compactlySupported {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (i : ℤ) :
    Module.Free Λ
        (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) ∧
      Module.Finite Λ
        (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) := by
  let _ := (Finite.isField_of_domain Λ).toField
  have := (nondegenerate_comp_unit_shift_of_isSepClosed _ i
    (finite_compactlySupportedCohomology Λ a K hK i)).1
  exact ⟨Module.Free.of_divisionRing _ _, Module.Finite.of_finite⟩

omit [QuasiCompact a] in
/-- At a finite field stage, over a separably closed field, `H^j(X, K^∨) = Hom(Λ_s, (Ra_* K^∨)[j])`
is a finite free `Λ`-module for `K ∈ D^b_{ctf}(X, Λ)`, `j = 2d - i`: it is dual to `H^i_c(X, K)`
(`AlgebraicGeometry.Etale.TateOrientation.isPerfPair_untwistedDegreewisePoincarePairing`). -/
lemma free_and_finite_hom_lowerStar_coefficientDual (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ (Spec (.of k)) (-d)) ≃ₗ[Λ]
      Λ) :
    Module.Free Λ (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) ∧
      Module.Finite Λ (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) := by
  let _ := (Finite.isField_of_domain Λ).toField
  have := γ.isPerfPair_untwistedDegreewisePoincarePairing hK i j hij ℓ
  obtain ⟨-, _⟩ := free_and_finite_hom_compactlySupported (a := a) hK i
  exact ⟨Module.Free.of_divisionRing _ _, Module.Finite.equiv
    ((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).flip.toPerfPair.symm⟩

/-- Blueprint `cor-pod-reciprocal-eigenvalues`: Reciprocal eigenvalues (finite-field stage).
This is also part (b) of blueprint `sk-thm-frobenius`.

**Reciprocal eigenvalues.** In the situation of
`AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap_of_isSepClosed`,
the eigenvalues of `F_{K^∨}` on `H^{2d-i}(X, K^∨)`, computed in an algebraically closed field `M`
containing `Λ` and counted with algebraic multiplicity, are the `q^d / α` for the eigenvalues
`α` of `F_{c,K}` on `H^i_c(X, K)`. No perfectness, finiteness or freeness hypothesis is needed:
the spaces are finite free (`AlgebraicGeometry.Etale.TateOrientation.free_and_finite_hom_compactlySupported`,
`AlgebraicGeometry.Etale.TateOrientation.free_and_finite_hom_lowerStar_coefficientDual`) and the
line-valued pairing is perfect
(`AlgebraicGeometry.Etale.TateOrientation.isPerfPair_untwistedDegreewisePoincarePairing`,
blueprint `thm-pod-degreewise-perfectness-over-a-field`). -/
theorem roots_map_charpoly_frobeniusOperator_of_isSepClosed (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ (Spec (.of k)) (-d)) ⟶
      tateObject Λ (Spec (.of k)) (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z)
    (hq : (q : Λ) ≠ 0) (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ (Spec (.of k)) (-d)) ≃ₗ[Λ]
      Λ)
    {M : Type*} [Field M] [IsAlgClosed M] (ι : Λ →+* M) :
    haveI := (free_and_finite_hom_compactlySupported (a := a) hK i).1
    haveI := (free_and_finite_hom_compactlySupported (a := a) hK i).2
    haveI := (free_and_finite_hom_lowerStar_coefficientDual γ hK i j hij ℓ).1
    haveI := (free_and_finite_hom_lowerStar_coefficientDual γ hK i j hij ℓ).2
    ((frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j)).charpoly.map
        ι).roots =
      ((frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)).charpoly.map
        ι).roots.map fun z ↦ ι ((q : Λ) ^ d) / z :=
  haveI := γ.isPerfPair_untwistedDegreewisePoincarePairing hK i j hij ℓ
  haveI := (free_and_finite_hom_compactlySupported (a := a) hK i).1
  haveI := (free_and_finite_hom_compactlySupported (a := a) hK i).2
  haveI := (free_and_finite_hom_lowerStar_coefficientDual γ hK i j hij ℓ).1
  haveI := (free_and_finite_hom_lowerStar_coefficientDual γ hK i j hij ℓ).2
  roots_map_charpoly_frobeniusOperator sq γ φ ψ hψ τ hTr q hτ (Finite.isField_of_domain Λ)
    hq i j hij ℓ ι

end FiniteField

end TateOrientation

end Etale

end AlgebraicGeometry
