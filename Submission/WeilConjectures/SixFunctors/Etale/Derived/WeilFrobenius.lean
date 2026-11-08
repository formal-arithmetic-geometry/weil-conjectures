/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Shift
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import Submission.WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Derived
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.KFlat
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- A morphism `u : M ⟶ N` is a *morphism of Weil objects* for Weil data `ψ_M` and `ψ_N` if
`ψ_N ∘ Lh^* u = u ∘ ψ_M`. -/
def IsWeilMorphism {M N : DerivedCategoryModule Λ Y}
    (ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M)
    (ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N) (f : M ⟶ N) : Prop :=
  (L((h)^*[ModuleCat.{u + 1} Λ])).map f ≫ ψN = ψM ≫ f

/-- A *Weil pairing* `P : A ⊗ᴸ B ⟶ C` is a morphism of Weil objects from `A ⊗ᴸ B`, with the
tensor product datum (`AlgebraicGeometry.Etale.tensorWeilDatum`), to `C`. -/
abbrev IsWeilPairing {A B C : DerivedCategoryModule Λ Y}
    (ψA : (L((h)^*[ModuleCat.{u + 1} Λ])).obj A ⟶ A)
    (ψB : (L((h)^*[ModuleCat.{u + 1} Λ])).obj B ⟶ B)
    (ψC : (L((h)^*[ModuleCat.{u + 1} Λ])).obj C ⟶ C)
    (P : ((derivedTensor _ Y).obj A).obj B ⟶ C) : Prop :=
  IsWeilMorphism h (tensorWeilDatum h ψA ψB) ψC P

variable {h} {M N P : DerivedCategoryModule Λ Y}
  {ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}
  {ψP : (L((h)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ P}

lemma IsWeilMorphism.comp {f : M ⟶ N} {f' : N ⟶ P} (hf : IsWeilMorphism h ψM ψN f)
    (hf' : IsWeilMorphism h ψN ψP f') : IsWeilMorphism h ψM ψP (f ≫ f') := by
  unfold IsWeilMorphism at *
  rw [Functor.map_comp, Category.assoc, hf', reassoc_of% hf]

lemma IsWeilPairing.comp {A B : DerivedCategoryModule Λ Y}
    {ψA : (L((h)^*[ModuleCat.{u + 1} Λ])).obj A ⟶ A}
    {ψB : (L((h)^*[ModuleCat.{u + 1} Λ])).obj B ⟶ B}
    {Q : ((derivedTensor _ Y).obj A).obj B ⟶ M} (hQ : IsWeilPairing h ψA ψB ψM Q)
    {f : M ⟶ N} (hf : IsWeilMorphism h ψM ψN f) : IsWeilPairing h ψA ψB ψN (Q ≫ f) :=
  IsWeilMorphism.comp hQ hf

/-- The *degreewise pairing* of a pairing `Q : A ⊗ᴸ B ⟶ C`,
`Hom(Λ_Y, A[i]) × Hom(Λ_Y, B[j]) ⟶ Hom(Λ_Y, C[i + j])`,
```
         λ⁻¹                  x ⊗ y                        ≅                     Q[i + j]
  Λ_Y ───────▶ Λ_Y ⊗ᴸ Λ_Y ─────────▶ A[i] ⊗ᴸ B[j] ─────▶ (A ⊗ᴸ B)[i + j] ──────────▶ C[i + j]
```
where the middle isomorphism moves the shifts out of the tensor product
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`). It is `Λ`-bilinear. -/
noncomputable def degreewisePairing {A B C : DerivedCategoryModule Λ Y}
    (Q : ((derivedTensor _ Y).obj A).obj B ⟶ C) (i j : ℤ) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ A⟦i⟧) →ₗ[Λ] (𝟙_ (DerivedCategoryModule Λ Y) ⟶ B⟦j⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ C⟦i + j⟧) :=
  LinearMap.mk₂ Λ
    (fun x y ↦ (derivedTensorLeftUnitor _ Y (𝟙_ _)).inv ≫
      ((derivedTensor _ Y).flip.obj (𝟙_ _)).map x ≫ ((derivedTensor _ Y).obj (A⟦i⟧)).map y ≫
        (derivedTensorShiftIso _ A B i j).hom ≫ Q⟦i + j⟧')
    (fun x x' y ↦ by rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add])
    (fun c x y ↦ by rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul])
    (fun x y y' ↦ by
      rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add])
    (fun c x y ↦ by
      rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul])

lemma degreewisePairing_apply {A B C : DerivedCategoryModule Λ Y}
    (Q : ((derivedTensor _ Y).obj A).obj B ⟶ C) (i j : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ A⟦i⟧) (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ B⟦j⟧) :
    degreewisePairing Q i j x y = (derivedTensorLeftUnitor _ Y (𝟙_ _)).inv ≫
      ((derivedTensor _ Y).flip.obj (𝟙_ _)).map x ≫ ((derivedTensor _ Y).obj (A⟦i⟧)).map y ≫
        (derivedTensorShiftIso _ A B i j).hom ≫ Q⟦i + j⟧' :=
  rfl

/-- **The degreewise pairing of a Weil pairing is Frobenius equivariant**: for a Weil pairing
`Q : A ⊗ᴸ B ⟶ C`, `x ∈ Hom(Λ_Y, A[i])` and `y ∈ Hom(Λ_Y, B[j])`,
`⟨F x, F y⟩ = F ⟨x, y⟩`, the Frobenius operators being those of the shifted data. -/
lemma IsWeilPairing.degreewisePairing_frobeniusOperator {A B C : DerivedCategoryModule Λ Y}
    {ψA : (L((h)^*[ModuleCat.{u + 1} Λ])).obj A ⟶ A}
    {ψB : (L((h)^*[ModuleCat.{u + 1} Λ])).obj B ⟶ B}
    {ψC : (L((h)^*[ModuleCat.{u + 1} Λ])).obj C ⟶ C}
    {Q : ((derivedTensor _ Y).obj A).obj B ⟶ C} (hQ : IsWeilPairing h ψA ψB ψC Q) (i j : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ A⟦i⟧) (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ B⟦j⟧) :
    degreewisePairing Q i j (frobeniusOperator h (shiftWeilDatum h ψA i) x)
        (frobeniusOperator h (shiftWeilDatum h ψB j) y) =
      frobeniusOperator h (shiftWeilDatum h ψC (i + j)) (degreewisePairing Q i j x y) := by
  simpa only [degreewisePairing_apply, frobeniusOperator_apply, shiftWeilDatum] using
    leftDerivedUpperStar_pairing_comm _ h ψA ψB ψC Q hQ i j x y

end Morphism

section Exchange

variable [Finite Λ] {a : X ⟶ Y} [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

/-- The Weil datum on `Ra_! K` of a Weil datum `φ : Lg^* K ⟶ K`, for `g ≫ a = a ≫ h`:
```
                Ex_!                     Ra_! φ
  Lh^* Ra_! K ───────▶ Ra_! Lg^* K ──────────▶ Ra_! K
```
with the compactly supported exchange map
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`). Over `Y = Spec k` its
Frobenius operators are the geometric Frobenius `F_{c,K}` on `H^i_c(X, K)`. -/
noncomputable def lowerShriekWeilDatum [QuasiCompact a] (sq : IsPullback g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ⟶
      (R(a)_![ModuleCat.{u + 1} Λ]).obj K :=
  (rightDerivedLowerShriekBaseChangeMap _ sq).app K ≫ (R(a)_![ModuleCat.{u + 1} Λ]).map φ

/-- The Weil datum on `Ra_* M` of a Weil datum `ψ : Lg^* M ⟶ M`, for `g ≫ a = a ≫ h`:
```
                Ex_*                     Ra_* ψ
  Lh^* Ra_* M ───────▶ Ra_* Lg^* M ──────────▶ Ra_* M
```
with the derived base change map (`AlgebraicGeometry.Etale.derivedBaseChangeMap`). Over
`Y = Spec k` its Frobenius operators are the geometric Frobenius on `H^j(X, M)`. -/
noncomputable def lowerStarWeilDatum (sq : CommSq g a a h) {M : DerivedCategoryModule Λ X}
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).obj ((R((a)_*[ModuleCat.{u + 1} Λ])).obj M) ⟶
      (R((a)_*[ModuleCat.{u + 1} Λ])).obj M :=
  (derivedBaseChangeMap _ sq).app M ≫ (R((a)_*[ModuleCat.{u + 1} Λ])).map ψ

variable {K L : DerivedCategoryModule Λ X}
  {φK : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K}
  {φL : (L((g)^*[ModuleCat.{u + 1} Λ])).obj L ⟶ L}

/-- Blueprint `lem-fix-weil-operations` (the cup product part).

**The mixed-support cup product is a Weil pairing**: for Weil data `φ` on `K` and `ψ` on `M`,
`⌣_c : Ra_! K ⊗ᴸ Ra_* M ⟶ Ra_!(K ⊗ᴸ M)` is a morphism of Weil objects for the induced data
`Ra_! φ`, `Ra_* ψ` and `Ra_!(φ ⊗ ψ)`. -/
lemma isWeilPairing_mixedSupportCupProduct [QuasiCompact a] (sq : IsPullback g a a h)
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj L ⟶ L) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ) (lowerStarWeilDatum sq.toCommSq ψ)
      (lowerShriekWeilDatum sq (tensorWeilDatum g φ ψ))
      (mixedSupportCupProduct (ModuleCat.{u + 1} Λ) a K L) :=
  mixedSupportCupProduct_exchange (ModuleCat.{u + 1} Λ) sq.toCommSq
    (rightDerivedLowerShriekBaseChangeMap Λ sq)
    (fun K M ↦ projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq K M) K L φ ψ

end Exchange

end Etale

end AlgebraicGeometry
