/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-!
# The degreewise Poincaré pairings

Let `γ` be a Tate orientation of `a : X ⟶ Y` of relative dimension `d`, and `K ∈ D(X_ét, Λ)`.
The derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

(`AlgebraicGeometry.Etale.TateOrientation.poincarePairing`) has degree zero. With the shift
convention `Hʳ(C[m]) = Hʳ⁺ᵐ(C)`, its degree-zero part pairs `Hⁱ_c(X, K)` with
`H⁻ⁱ(RΓ(X, K^∨(d))[2d]) = H^{2d-i}(X, K^∨(d))`, giving the pairings

`⟨-, -⟩ᵢ : Hⁱ_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ`.

Eliminating the invertible twist `Λ(d)` of the second factor, the same morphism gives the
line-valued pairings `Hⁱ_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)`.

As in `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup`, cohomology classes are
morphisms out of the unit: a class in `Hⁿ_c(X, K)` is a morphism `Λ_Y ⟶ (Ra_! K)[n]` and a
class in `Hⁿ(X, M)` a morphism `Λ_Y ⟶ (Ra_* M)[n]` of `D(Y_ét, Λ)`; for `Y = Spec k` with `k`
separably closed these are the cohomology groups, and `Hom(Λ_Y, Λ_Y(m)) = Λ(m)`.

## Main definitions

All of them are blueprint `prop-pod-degree-of-the-pairing`.

- `AlgebraicGeometry.Etale.TateOrientation.degreeZeroPairing`: the degree-zero part of `β_K`,
  pairing `Hⁱ_c(X, K)` with `H⁻ⁱ(RΓ(X, K^∨(d))[2d])`.
- `AlgebraicGeometry.Etale.TateOrientation.degreewisePairing`: the pairings
  `⟨-, -⟩ᵢ : Hⁱ_c(X, K) × Hʲ(X, K^∨(d)) ⟶ Λ` for `i + j = 2d`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePairing`: the line-valued
  pairings `Hⁱ_c(X, K) × Hʲ(X, K^∨) ⟶ Λ(-d)` for `i + j = 2d`.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePairing_apply`: `⟨x, y⟩ᵢ` is the
  degree-zero part of `β_K` evaluated on `x` and on `y` read in `H⁻ⁱ(RΓ(X, K^∨(d))[2d])`.

## Implementation notes

The Hom groups of `D(Y_ét, Λ)` carry no `Λ`-module structure in the repository, so the
pairings are biadditive rather than `Λ`-bilinear. The complementary degrees are two integers
`i j` with `i + j = 2d`, `2d - (2d - i)` not being definitionally `i`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- The derived category `D(Y_ét, A)` of `A`-valued étale sheaves on `Y`. -/
local notation "𝐃(" Y ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology Y) A)

/-- The degree-zero part of a pairing `β : C ⊗ᴸ D ⟶ Λ_Y`, applied to classes
`x : Λ_Y ⟶ C[i]` and `y : S ⟶ D[-i]`:
```
      λ⁻¹               x ⊗ y                     ≅                 ≅            β
S ─────────▶ Λ_Y ⊗ᴸ S ────────▶ C[i] ⊗ᴸ D[-i] ─────▶ (C ⊗ᴸ D)[i - i] ─────▶ C ⊗ᴸ D ─────▶ Λ_Y
``` -/
noncomputable def pairingAux {C D S : 𝐃(Y, A)} (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _)
    {i : ℤ} (x : 𝟙_ _ ⟶ C⟦i⟧) (y : S ⟶ D⟦-i⟧) : S ⟶ 𝟙_ _ :=
  (derivedTensorLeftUnitor A Y S).inv ≫ ((derivedTensor A Y).map x).app S ≫
    ((derivedTensor A Y).obj (C⟦i⟧)).map y ≫ (derivedTensorShiftIso A C D i (-i)).hom ≫
      (shiftFunctorZero' _ (i + -i) (add_neg_cancel i)).hom.app _ ≫ β

lemma pairingAux_add_left {C D S : 𝐃(Y, A)} (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _)
    {i : ℤ} (x x' : 𝟙_ _ ⟶ C⟦i⟧) (y : S ⟶ D⟦-i⟧) :
    pairingAux β (x + x') y = pairingAux β x y + pairingAux β x' y := by
  simp [pairingAux, derivedTensor]

lemma pairingAux_add_right {C D S : 𝐃(Y, A)} (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _)
    {i : ℤ} (x : 𝟙_ _ ⟶ C⟦i⟧) (y y' : S ⟶ D⟦-i⟧) :
    pairingAux β x (y + y') = pairingAux β x y + pairingAux β x y' := by
  simp [pairingAux, derivedTensor, MonoidalPreadditive.whiskerLeft_add]

/-- The degree-zero part of a pairing `β : C ⊗ᴸ D ⟶ Λ_Y` in degree `i`, as a biadditive map
`Hom(Λ_Y, C[i]) × Hom(S, D[-i]) ⟶ Hom(S, Λ_Y)` (`AlgebraicGeometry.Etale.pairingAux`). -/
noncomputable def pairing {C D : 𝐃(Y, A)} (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _)
    (i : ℤ) (S : 𝐃(Y, A)) :
    ((𝟙_ 𝐃(Y, A)) ⟶ C⟦i⟧) →+ (S ⟶ D⟦-i⟧) →+ (S ⟶ 𝟙_ 𝐃(Y, A)) :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (pairingAux β x) (pairingAux_add_right β x))
    fun x x' ↦ by
      ext y
      exact pairingAux_add_left β x x' y

end General

namespace TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] {d : ℕ}

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The degree-zero part of the derived Poincaré pairing `β_K` of a Tate orientation `γ`
(`AlgebraicGeometry.Etale.TateOrientation.poincarePairing`): the biadditive pairing of
`Hⁱ_c(X, K)` with `H⁻ⁱ(RΓ(X, K^∨(d))[2d])` with values in `Hom(Λ_Y, Λ_Y) = Λ`. -/
noncomputable def degreeZeroPairing (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X)
    (i : ℤ) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦(2 * d : ℤ)⟧)⟦-i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  pairing (γ.poincarePairing K) i _

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The degreewise Poincaré pairings `⟨-, -⟩ᵢ : Hⁱ_c(X, K) × Hʲ(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`: the
degree-zero part of the derived Poincaré pairing
(`AlgebraicGeometry.Etale.TateOrientation.degreeZeroPairing`), with a class of
`Hʲ(X, K^∨(d))` read in `H⁻ⁱ(RΓ(X, K^∨(d))[2d])` through `M[j] ≅ M[2d][-i]`. -/
noncomputable def degreewisePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  (γ.degreeZeroPairing K i).compl₂ (Preadditive.rightComp _
    ((shiftFunctorAdd' _ (2 * d : ℤ) (-i) j (by lia)).hom.app _))

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The degreewise pairing `⟨x, y⟩ᵢ` is the degree-zero part of `β_K` evaluated on `x` and on the
class `y` read in degree `-i` of `RΓ(X, K^∨(d))[2d]`, by the shift convention
`H⁻ⁱ(M[2d]) = H^{2d-i}(M)`. -/
theorem degreewisePairing_apply (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : (𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : (𝟙_ (DerivedCategoryModule Λ Y)) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePairing K i j hij x y = γ.degreeZeroPairing K i x
      (y ≫ (shiftFunctorAdd' _ (2 * d : ℤ) (-i) j (by lia)).hom.app _) :=
  rfl

/-- The *untwisting* of a class `y ∈ Hʲ(X, K^∨)`: the morphism `Λ_Y(d) ⟶ (Ra_*(K^∨(d)))[j]`
obtained by tensoring `y` with `Λ_Y(d)` and applying the projection map of `Ra_*` together with
`La^* Λ_Y(d) ≅ Λ_X(d)`:
```
            λ⁻¹                   y ⊗ 1                      ≅
Λ_Y(d) ──────▶ Λ_Y ⊗ᴸ Λ_Y(d) ─────────▶ (Ra_* K^∨)[j] ⊗ᴸ Λ_Y(d) ──▶ (Ra_* K^∨ ⊗ᴸ Λ_Y(d))[j]
       projection map                                    ≅
     ──────────────▶ (Ra_*(K^∨ ⊗ᴸ La^* Λ_Y(d)))[j] ─────────▶ (Ra_*(K^∨ ⊗ᴸ Λ_X(d)))[j]
```
This is the identification `Hʲ(X, K^∨(d)) ≅ Hʲ(X, K^∨) ⊗ Λ(d)`. -/
noncomputable def untwistClass (K : DerivedCategoryModule Λ X) (j : ℤ) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →+
      (tateObject Λ Y d ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :=
  (Preadditive.rightComp _
    ((((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso j).hom.app _ ≫
      (((rightDerivedLowerStarProjectionMap _ a).app
        ((DerivedCategory.coefficientDual _ X).obj (op K))).app (tateObject Λ Y d))⟦j⟧' ≫
      ((R((a)_*[ModuleCat.{u + 1} Λ])).map (((derivedTensor _ X).obj _).map
        (leftDerivedUpperStarTateObjectIso a d).hom))⟦j⟧')).comp
    ((Preadditive.leftComp _ (derivedTensorLeftUnitor _ Y (tateObject Λ Y d)).inv).comp
      (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).mapAddHom))

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The line-valued Poincaré pairings `Hⁱ_c(X, K) × Hʲ(X, K^∨) ⟶ Λ(-d)`, `i + j = 2d`, obtained
from the same morphism `β_K` by eliminating the twist `Λ_X(d)` of the second factor: the
untwisting `y ↦ Λ_Y(d) ⟶ (Ra_*(K^∨(d)))[j]`
(`AlgebraicGeometry.Etale.TateOrientation.untwistClass`) is paired with `x` by the degree-zero
part of `β_K`, which gives a morphism `Λ_Y(d) ⟶ Λ_Y`, and this is tensored with the twist
inverse `Λ_Y(-d)` and read through `Λ_Y ≅ Λ_Y(d) ⊗ᴸ Λ_Y(-d)`. -/
noncomputable def untwistedDegreewisePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ tateObject Λ Y (-d)) :=
  ((pairing (γ.poincarePairing K) i (tateObject Λ Y d)).compl₂
    ((Preadditive.rightComp _ ((shiftFunctorAdd' _ (2 * d : ℤ) (-i) j (by lia)).hom.app _)).comp
      (untwistClass K j))).compr₂
    ((Preadditive.leftComp _ (constantComplexIsoTateObjectTensor Y d).hom).comp
      ((Preadditive.rightComp _ (derivedTensorLeftUnitor _ Y (tateObject Λ Y (-d))).hom).comp
        ((derivedTensor _ Y).flip.obj (tateObject Λ Y (-d))).mapAddHom))

end TateOrientation

end Etale

end AlgebraicGeometry
