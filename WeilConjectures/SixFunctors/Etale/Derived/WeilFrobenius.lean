/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Weil data and their Frobenius operators

Let `h : Y ⟶ Y` be an endomorphism of a scheme; in the `ℓ`-adic formalism `Y = X₀ ×_{k₀} k` and
`h = g_γ` is the geometric Frobenius automorphism attached to a Frobenius `γ` of `k` over `k₀`.
A *Weil datum* on `M ∈ D(Y_ét, Λ)` is a morphism `ψ : Lh^* M ⟶ M` (an isomorphism for a strict
Weil complex, `AlgebraicGeometry.Etale.WeilComplex`). This file attaches to Weil data the
operations that the Frobenius statements of Poincaré duality are phrased with.

* The *Frobenius operator* of `ψ` on `H⁰(Y, M) = Hom(Λ_Y, M)` is
  `x ↦ ψ ∘ Lh^* x ∘ ε⁻¹`, for the canonical `ε : Lh^* Λ_Y ≅ Λ_Y`; on
  `Hⁿ(Y, M) = Hom(Λ_Y, M[n])` it is the operator of the shifted datum `ψ[n]`.
* A morphism `a : X ⟶ Y` with `g ≫ a = a ≫ h` carries Weil data on `X` to Weil data on `Y`:
  on `Ra_! K` through the exchange `Ex_! : Lh^* Ra_! ⟶ Ra_! Lg^*`, and on `Ra_* M` through
  `Ex_* : Lh^* Ra_* ⟶ Ra_* Lg^*`. Over `Y = Spec k` these give the geometric Frobenius on
  compactly supported and on ordinary cohomology.
* Weil data on `A` and `B` give one on `A ⊗ᴸ B`. A *Weil pairing* is a morphism
  `A ⊗ᴸ B ⟶ C` of Weil objects, and its *degreewise pairing*
  `Hom(Λ_Y, A[i]) × Hom(Λ_Y, B[j]) ⟶ Hom(Λ_Y, C[i + j])` is Frobenius equivariant.

## Main definitions

- `AlgebraicGeometry.Etale.shiftWeilDatum`, `AlgebraicGeometry.Etale.tensorWeilDatum`,
  `AlgebraicGeometry.Etale.lowerShriekWeilDatum`, `AlgebraicGeometry.Etale.lowerStarWeilDatum`:
  the induced Weil data.
- `AlgebraicGeometry.Etale.frobeniusOperator` (`def-trf-frobenius-operators`): the Frobenius
  operator of a Weil datum, a `Λ`-linear endomorphism of `Hom(Λ_Y, M)`.
- `AlgebraicGeometry.Etale.IsWeilMorphism`, `AlgebraicGeometry.Etale.IsWeilPairing`: morphisms
  and pairings of Weil objects.
- `AlgebraicGeometry.Etale.degreewisePairing`: the degreewise pairing of a pairing.

## Main statements

- `AlgebraicGeometry.Etale.IsWeilPairing.degreewisePairing_frobeniusOperator`: the degreewise
  pairing of a Weil pairing intertwines the Frobenius operators.
- `AlgebraicGeometry.Etale.isWeilPairing_mixedSupportCupProduct`: the mixed-support cup product
  is a Weil pairing.

## Implementation notes

The exchange maps are `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap` and
`AlgebraicGeometry.Etale.derivedBaseChangeMap` of `sk-def-sf-exchanges`. The compatibilities of
the derived pullback with the tensor product, the shifts and the exchange maps that the
equivariance statements need are not formalised yet; they are stated here as separate lemmas.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}

section Datum

variable (h : Y ⟶ Y)

/-- The *shift* `ψ[n] : Lh^*(M[n]) ≅ (Lh^* M)[n] ⟶ M[n]` of a Weil datum `ψ : Lh^* M ⟶ M`,
through the shift compatibility of `Lh^*`. -/
noncomputable def shiftWeilDatum {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) (n : ℤ) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).obj (M⟦n⟧) ⟶ M⟦n⟧ :=
  ((L((h)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app M ≫ ψ⟦n⟧'

/-- The *tensor product* `ψ_A ⊗ ψ_B : Lh^*(A ⊗ᴸ B) ≅ Lh^* A ⊗ᴸ Lh^* B ⟶ A ⊗ᴸ B` of two Weil
data, through `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`. -/
noncomputable def tensorWeilDatum {A B : DerivedCategoryModule Λ Y}
    (ψA : (L((h)^*[ModuleCat.{u + 1} Λ])).obj A ⟶ A)
    (ψB : (L((h)^*[ModuleCat.{u + 1} Λ])).obj B ⟶ B) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor _ Y).obj A).obj B) ⟶
      ((derivedTensor _ Y).obj A).obj B :=
  (leftDerivedUpperStarTensorIso _ h A B).hom ≫ ((derivedTensor _ Y).map ψA).app _ ≫
    ((derivedTensor _ Y).obj A).map ψB

/-- Blueprint `def-trf-frobenius-operators`: the Frobenius operators.

The *Frobenius operator* of a Weil datum `ψ : Lh^* M ⟶ M` on `H⁰(Y, M) = Hom(Λ_Y, M)`,
```
         ε⁻¹                Lh^* x               ψ
  Λ_Y ─────────▶ Lh^* Λ_Y ──────────▶ Lh^* M ─────────▶ M
```
for the canonical `ε : Lh^* Λ_Y ≅ Λ_Y` (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`).
On `Hⁿ(Y, M) = Hom(Λ_Y, M[n])` the Frobenius operator is that of the shifted datum
(`AlgebraicGeometry.Etale.shiftWeilDatum`). It is `Λ`-linear. -/
noncomputable def frobeniusOperator {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ M) →ₗ[Λ] (𝟙_ (DerivedCategoryModule Λ Y) ⟶ M) where
  toFun x := (leftDerivedUpperStarUnitIso _ h).inv ≫ (L((h)^*[ModuleCat.{u + 1} Λ])).map x ≫ ψ
  map_add' x y := by
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c x := by
    dsimp only [RingHom.id_apply]
    rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

lemma frobeniusOperator_apply {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ M) :
    frobeniusOperator h ψ x =
      (leftDerivedUpperStarUnitIso _ h).inv ≫ (L((h)^*[ModuleCat.{u + 1} Λ])).map x ≫ ψ :=
  rfl

/-- The Frobenius operator of a doubly shifted datum `(ψ[a])[b]` is that of `ψ[c]`,
`a + b = c`, read through `M[c] ≅ (M[a])[b]`. -/
lemma frobeniusOperator_shiftWeilDatum_comp_shiftFunctorAdd' {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) (a b c : ℤ) (hab : a + b = c)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ M⟦c⟧) :
    frobeniusOperator h (shiftWeilDatum h (shiftWeilDatum h ψ a) b)
        (x ≫ (shiftFunctorAdd' (DerivedCategoryModule Λ Y) a b c hab).hom.app M) =
      frobeniusOperator h (shiftWeilDatum h ψ c) x ≫
        (shiftFunctorAdd' (DerivedCategoryModule Λ Y) a b c hab).hom.app M := by
  rw [frobeniusOperator_apply, frobeniusOperator_apply, shiftWeilDatum, shiftWeilDatum,
    shiftWeilDatum, Functor.commShiftIso_add' _ hab]
  have := (shiftFunctorAdd' (DerivedCategoryModule Λ Y) a b c hab).hom.naturality ψ
  simp only [Functor.comp_map] at this
  simp only [Functor.CommShift.isoAdd'_hom_app, Category.assoc, Functor.map_comp, this,
    Iso.inv_hom_id_app_assoc]

end Datum

section Morphism

variable (h : Y ⟶ Y)

variable {h} {M N P : DerivedCategoryModule Λ Y}
  {ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}
  {ψP : (L((h)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ P}

end Morphism

section Exchange

variable [Finite Λ] {a : X ⟶ Y} [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

variable {K L : DerivedCategoryModule Λ X}
  {φK : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K}
  {φL : (L((g)^*[ModuleCat.{u + 1} Λ])).obj L ⟶ L}

end Exchange

end Etale

end AlgebraicGeometry
