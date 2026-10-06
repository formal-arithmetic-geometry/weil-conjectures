/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Classes
public import WeilConjectures.EtaleCohomology.PoincareDuality.Finiteness
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing
public import WeilConjectures.Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Degreewise duality over a field

The derived Poincaré pairing `β_K` of a Tate orientation can be read degree by degree. The
result is a family of pairings

`⟨-,-⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`,

which are perfect over a field `Λ` of coefficients.

Classes are the morphisms `Λ_Y ⟶ M[i]`, elements of `CategoryTheory.ShiftedHom Λ_Y M i`, for
`M = Ra_! K` and `M = Ra_*(K^∨(d))` in `D(Y_ét, Λ)`. The pairing of `x` and `y` is the pairing
of classes (`AlgebraicGeometry.Etale.shiftedHomPairing`) induced by `β_K`, after reading
`y ∈ H^j(X, K^∨(d))` as a class of degree `j - 2d` of `(Ra_*(K^∨(d)))[2d]`. It is `Λ`-valued
for a connected `Y`, through `AlgebraicGeometry.Etale.coefficientAlgEquiv`. The two degrees are
separate indices `i j : ℤ` with `i + j = 2 * d`, since `2 * d - (2 * d - i)` is not
definitionally `i`.

Degreewise duality is then a consequence of two statements: derived Poincaré duality
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`), and, at a
separably closed point, the perfectness on classes of a perfect pairing of dualizable complexes
over a field (`AlgebraicGeometry.Etale.isPerfPair_shiftedHomPairing`), applied to `β_K`;
`Ra_! K` is dualizable by finiteness
(`AlgebraicGeometry.Etale.isDualizable_rightDerivedLowerShriek`).

## Main definitions

- `AlgebraicGeometry.Etale.degreewisePoincarePairing`: the degreewise pairing `⟨-,-⟩_i`.
- `AlgebraicGeometry.Etale.twistLowerStarClass`: a class of `Ra_* M` twisted by `Λ(d)`.
- `AlgebraicGeometry.Etale.untwistedDegreewisePoincarePairing`: the line-valued form
  `H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)` of the degreewise pairing.

## Main statements

- `AlgebraicGeometry.Etale.isPerfPair_degreewisePoincarePairing`: `⟨-,-⟩_i` is perfect.
- `AlgebraicGeometry.Etale.isPerfPair_degreewisePoincarePairing_of_isProper`: for proper `X`,
  the same with `H_c` replaced by `H`.
- `AlgebraicGeometry.Etale.exists_untwistedDegreewisePoincarePairing_eq`: the line-valued form
  is the degreewise pairing up to linear isomorphisms `H^j(X, K^∨) ≅ H^j(X, K^∨(d))` and
  `Λ ≅ Λ(-d)` (blueprint, *Degree of the pairing*).
- `AlgebraicGeometry.Etale.bijective_untwistedDegreewisePoincarePairing`,
  `AlgebraicGeometry.Etale.bijective_untwistedDegreewisePoincarePairing_flip`: the line-valued
  form is perfect.

## Implementation notes

The blueprint's field stages are `E` and `ℚ̄_ℓ`. Neither carries the six operations in the
repository (see `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`), so they are **not
covered** here. The field statements are for `ModuleCat Λ` with `Λ` a *finite* field, i.e.
`Λ = 𝔽_ℓ`-algebras that are fields: finiteness of `Λ` is what the six operations and the
finiteness theorem (`AlgebraicGeometry.Etale.isDualizable_rightDerivedLowerShriek`) need.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Definitions

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X Y : Scheme.{u}} (a : X ⟶ Y)
  {d : ℕ}

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

The *degreewise Poincaré pairing* of a Tate orientation `γ` of `a : X ⟶ Y`, for a connected
`Y`,

`⟨-,-⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`:

the pairing of classes induced by `β_K` (`AlgebraicGeometry.Etale.shiftedHomPairing`),
the class `y` of degree `j` of `Ra_*(K^∨(d))` being read as a class of degree `j - 2d` of
`(Ra_*(K^∨(d)))[2d]` (`CategoryTheory.ShiftedHom.shiftLinearEquiv`),
```
                    x ⊗ᴸ y
Λ_Y ≅ Λ_Y ⊗ᴸ Λ_Y ─────────▶ (Ra_! K)[i] ⊗ᴸ ((Ra_*(K^∨(d)))[2d])[j - 2d]
                       ≅                                         β_K[0]
                 ─────────▶ (Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d])[0] ─────────▶ Λ_Y[0] ≅ Λ_Y
```
read in `Λ` through `AlgebraicGeometry.Etale.coefficientAlgEquiv`. -/
noncomputable def degreewisePoincarePairing [HasCompactification a] [ConnectedSpace Y]
    (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i →ₗ[Λ]
      ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K)) j →ₗ[Λ] Λ :=
  (shiftedHomPairing (γ.poincarePairing K) i (j - 2 * d) (by omega)).compl₂
    (ShiftedHom.shiftLinearEquiv Λ _ _ (2 * d : ℤ) (j - 2 * d) j (by omega)).symm.toLinearMap

lemma degreewisePoincarePairing_apply [HasCompactification a] [ConnectedSpace Y]
    (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i)
    (y : ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K)) j) :
    degreewisePoincarePairing Λ a γ K i j hij x y =
      shiftedHomPairing (γ.poincarePairing K) i (j - 2 * d) (by omega) x
        ((ShiftedHom.shiftLinearEquiv Λ _ _ (2 * d : ℤ) (j - 2 * d) j (by omega)).symm y) :=
  rfl

variable (d) in
/-- A class `y ∈ H^j(Y, Ra_* M)` twisted into a morphism `Λ_Y(d) ⟶ (Ra_*(M ⊗ᴸ Λ_X(d)))[j]`:
```
         λ⁻¹                        y ⊗ᴸ 1                              ≅
Λ_Y(d) ─────▶ Λ_Y ⊗ᴸ Λ_Y(d) ─────────────▶ (Ra_* M)[j] ⊗ᴸ Λ_Y(d) ─────▶ (Ra_* M ⊗ᴸ Λ_Y(d))[j]
                  projection map                                ≅
         ─────────────────────────▶ (Ra_*(M ⊗ᴸ La^* Λ_Y(d)))[j] ─────▶ (Ra_*(M ⊗ᴸ Λ_X(d)))[j]
```
through the projection map of `Ra_*` and `La^* Λ_Y(d) ≅ Λ_X(d)`. It is `Λ`-linear, being built
from composition and the `Λ`-linear functor `- ⊗ᴸ Λ_Y(d)`. -/
noncomputable def twistLowerStarClass (M : DerivedCategoryModule Λ X) (j : ℤ) :
    ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj M) j →ₗ[Λ]
      (tateObject Λ Y d ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor _ X).obj M).obj (tateObject Λ X d)))⟦j⟧) :=
  Linear.leftComp Λ _ (derivedTensorLeftUnitor _ Y _).inv ∘ₗ
    Linear.rightComp Λ _
      ((((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso j).hom.app _ ≫
        (((rightDerivedLowerStarProjectionMap _ a).app M).app _ ≫
          (R((a)_*[ModuleCat.{u + 1} Λ])).map (((derivedTensor _ X).obj M).map
            (leftDerivedUpperStarTateObjectIso a d).hom))⟦j⟧') ∘ₗ
      ((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).mapLinearMap Λ

lemma twistLowerStarClass_apply (M : DerivedCategoryModule Λ X) (j : ℤ)
    (y : ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj M) j) :
    twistLowerStarClass Λ a d M j y = (derivedTensorLeftUnitor _ Y _).inv ≫
      ((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).map y ≫
        (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso j).hom.app _ ≫
          (((rightDerivedLowerStarProjectionMap _ a).app M).app _ ≫
            (R((a)_*[ModuleCat.{u + 1} Λ])).map (((derivedTensor _ X).obj M).map
              (leftDerivedUpperStarTateObjectIso a d).hom))⟦j⟧' :=
  rfl

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

The *line-valued* form of the degreewise Poincaré pairing,

`H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`, `i + j = 2d`,

with values in the classes `Λ_Y ⟶ Λ_Y(-d)`: the class `y ∈ H^j(X, K^∨)` is twisted into
`Λ_Y(d) ⟶ (Ra_*(K^∨(d)))[j]` (`AlgebraicGeometry.Etale.twistLowerStarClass`), paired with
`x` along `β_K` into `Λ_Y(d) ⟶ Λ_Y` (`AlgebraicGeometry.Etale.cupProduct`), and the
result untwisted (`AlgebraicGeometry.Etale.untwistTateObject`). -/
noncomputable def untwistedDegreewisePoincarePairing [HasCompactification a]
    (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i →ₗ[Λ]
      ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))) j →ₗ[Λ]
        (𝟙_ _ ⟶ tateObject Λ Y (-d)) :=
  ((cupProduct Λ (γ.poincarePairing K) i (j - 2 * d) 0 (by omega)).compl₂
      ((ShiftedHom.shiftLinearEquiv Λ _ _ (2 * d : ℤ) (j - 2 * d) j (by omega)).symm.toLinearMap ∘ₗ
        twistLowerStarClass Λ a d _ j)).compr₂
    (untwistTateObject Λ Y d ∘ₗ (Linear.homCongr Λ (derivedTensorLeftUnitor _ Y _)
      ((shiftFunctorZero _ ℤ).app _)).toLinearMap)

lemma untwistedDegreewisePoincarePairing_apply [HasCompactification a]
    (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i)
    (y : ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))) j) :
    untwistedDegreewisePoincarePairing Λ a γ K i j hij x y = untwistTateObject Λ Y d
      (((derivedTensorLeftUnitor _ Y _).inv ≫
        cupProduct Λ (γ.poincarePairing K) i (j - 2 * d) 0 (by omega) x
          ((ShiftedHom.shiftLinearEquiv Λ _ _ (2 * d : ℤ) (j - 2 * d) j (by omega)).symm
            (twistLowerStarClass Λ a d _ j y))) ≫ (shiftFunctorZero _ ℤ).hom.app _) :=
  rfl

end Definitions

section Statements

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}}
  {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  (a : X ⟶ Spec (.of k)) [HasCompactification a] [QuasiCompact a] {d : ℕ}
  (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
  (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K)

include hK hKd in
/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**Degreewise duality.** For `a : X ⟶ Spec k` separated of finite type over a separably closed
field, a finite field `Λ` of coefficients and `K ∈ D^b_{ctf}(X, Λ)` dualizable, the
degreewise Poincaré pairings

`⟨-,-⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`,

are perfect. -/
theorem isPerfPair_degreewisePoincarePairing (hΛ : IsField Λ) (i j : ℤ) (hij : i + j = 2 * d) :
    (degreewisePoincarePairing Λ a γ K i j hij).IsPerfPair :=
  (isPerfPair_shiftedHomPairing Λ hΛ (γ.poincarePairing K)
    (isDualizable_rightDerivedLowerShriek Λ a hK) (γ.isPerfectPairing_poincarePairing hK hKd)
    i (j - 2 * d) (by omega)).compl₂_equiv (ShiftedHom.shiftLinearEquiv Λ _ _ _ _ _ _).symm

include hK hKd in
/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The proper case.** For `X` proper, the same holds with `H_c` replaced by `H`: the pairing
`H^i(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, obtained from `⟨-,-⟩_i` through the identification
`H^i(X, K) ≅ H^i_c(X, K)` of `Ra_* ≅ Ra_!`
(`AlgebraicGeometry.Etale.lowerStarClassEquivLowerShriek`), is perfect:
```
                  (H ≅ H_c) × id                                    ⟨-,-⟩_i
H^i(X, K) × H^j(X, K^∨(d)) ──────────▶ H^i_c(X, K) × H^j(X, K^∨(d)) ───────▶ Λ
```
-/
theorem isPerfPair_degreewisePoincarePairing_of_isProper [IsProper a] (hΛ : IsField Λ)
    (i j : ℤ) (hij : i + j = 2 * d) :
    ((degreewisePoincarePairing Λ a γ K i j hij).comp
      (lowerStarClassEquivLowerShriek (ModuleCat.{u + 1} Λ) Λ a K i).toLinearMap).IsPerfPair :=
  (isPerfPair_degreewisePoincarePairing Λ a γ hK hKd hΛ i j hij).comp_equiv
    (lowerStarClassEquivLowerShriek (ModuleCat.{u + 1} Λ) Λ a K i)

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The line-valued form is the degreewise pairing** (blueprint, *Degree of the pairing*). Over a
separably closed field, the untwisted pairing `H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)` is the
degreewise pairing `⟨-,-⟩_i` read through linear isomorphisms `f` and `e`:
```
                       id × f                                  ⟨-,-⟩_i          e
H^i_c(X, K) × H^j(X, K^∨) ───────▶ H^i_c(X, K) × H^j(X, K^∨(d)) ────────▶ Λ ─────▶ Λ(-d)
```
-/
theorem exists_untwistedDegreewisePoincarePairing_eq (i j : ℤ) (hij : i + j = 2 * d) :
    ∃ (f : ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))) j ≃ₗ[Λ]
          ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K)) j)
      (e : Λ ≃ₗ[Λ] (𝟙_ _ ⟶ tateObject Λ (Spec (.of k)) (-d))),
      untwistedDegreewisePoincarePairing Λ a γ K i j hij =
        ((degreewisePoincarePairing Λ a γ K i j hij).compl₂ f.toLinearMap).compr₂ e.toLinearMap :=
  -- Proof sketch: since `k` is separably closed, the Tate object `Λ(d)` on `Spec k` is
  -- trivial; choose `t : Λ ≅ Λ(d)`. Then `f` is `y ↦ (twistLowerStarClass y) ∘ t`, a
  -- bijection as `Λ_Y(d)` is invertible, and `e` is `r ↦ untwistTateObject (r • t⁻¹)`.
  -- Both pairings are then the same composite `β_K ∘ (x ⊗ᴸ y)`, before and after inserting
  -- the twist, and agree by naturality of the projection map.
  sorry

include hK hKd in
/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The line-valued form.** For a finite field `Λ` of coefficients and `K ∈ D^b_{ctf}(X, Λ)`
dualizable, the untwisted pairing `H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)` is perfect in the first
variable: its adjoint `H^i_c(X, K) → Hom(H^j(X, K^∨), Λ(-d))` is bijective. -/
theorem bijective_untwistedDegreewisePoincarePairing (hΛ : IsField Λ) (i j : ℤ)
    (hij : i + j = 2 * d) :
    Function.Bijective (untwistedDegreewisePoincarePairing Λ a γ K i j hij) := by
  obtain ⟨f, e, h⟩ := exists_untwistedDegreewisePoincarePairing_eq Λ a γ i j hij
  have := (isPerfPair_degreewisePoincarePairing Λ a γ hK hKd hΛ i j hij).compl₂_equiv f
  rw [h]
  exact LinearMap.bijective_compr₂_of_equiv _ e (LinearMap.IsPerfPair.bijective_left
    ((degreewisePoincarePairing Λ a γ K i j hij).compl₂ f.toLinearMap))

include hK hKd in
/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The line-valued form.** For a finite field `Λ` of coefficients and `K ∈ D^b_{ctf}(X, Λ)`
dualizable, the untwisted pairing `H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)` is perfect in the second
variable: its adjoint `H^j(X, K^∨) → Hom(H^i_c(X, K), Λ(-d))` is bijective. -/
theorem bijective_untwistedDegreewisePoincarePairing_flip (hΛ : IsField Λ) (i j : ℤ)
    (hij : i + j = 2 * d) :
    Function.Bijective (untwistedDegreewisePoincarePairing Λ a γ K i j hij).flip := by
  obtain ⟨f, e, h⟩ := exists_untwistedDegreewisePoincarePairing_eq Λ a γ i j hij
  have := (isPerfPair_degreewisePoincarePairing Λ a γ hK hKd hΛ i j hij).compl₂_equiv f
  rw [h]
  exact LinearMap.bijective_compr₂_of_equiv _ e (LinearMap.IsPerfPair.bijective_right
    ((degreewisePoincarePairing Λ a γ K i j hij).compl₂ f.toLinearMap))

end Statements

end Etale

end AlgebraicGeometry
