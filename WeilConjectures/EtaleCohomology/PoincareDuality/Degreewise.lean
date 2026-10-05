/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Classes
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.Proper
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Degreewise duality over a field

Over a field of coefficients a perfect point complex is the direct sum of its shifted
cohomologies, so the derived Poincaré pairing `β_K` of
`WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` can be read degree by degree. The
result is a family of perfect pairings

`⟨-,-⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ`.

Classes are the morphisms `Λ_s ⟶ M[i]` of
`AlgebraicGeometry.Etale.DerivedCategory.cohomologyClasses`, for `M = Ra_! K` and
`M = Ra_* (K^∨(d))` in `D(s_ét, Λ)`. The pairing of `x` and `y` is the composite

`Λ_s ≅ Λ_s ⊗ Λ_s ⟶ (Ra_! K)[i] ⊗ (Ra_* K^∨(d))[j] ≅ (Ra_! K ⊗ Ra_* K^∨(d))[i + j] ⟶ Λ_s`

with `i + j = 2d`, the last map being `β_K` read through the identification of the shift.
It lands in `End (Λ_s)`, which is `Λ` by `AlgebraicGeometry.Etale.coefficientRingEquiv`.
The two degrees are separate indices `i j : ℤ` with `i + j = 2 * d`, since
`2 * d - (2 * d - i)` is not definitionally `i`.

## Main definitions

- `AlgebraicGeometry.Etale.degreewisePoincarePairing`: the degreewise pairing `⟨-,-⟩_i`.
- `AlgebraicGeometry.Etale.untwistedDegreewisePoincarePairing`: its line-valued form,
  `H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`: `β_K` is perfect.
- `AlgebraicGeometry.Etale.isPerfPair_degreewisePoincarePairing`: `⟨-,-⟩_i` is perfect.
- `AlgebraicGeometry.Etale.isPerfPair_untwistedDegreewisePoincarePairing`: the line-valued
  form is perfect.
- `AlgebraicGeometry.Etale.isPerfPair_degreewisePoincarePairing_of_isProper`: for proper `X`,
  the same with `H_c` replaced by `H`.

## Implementation notes

The blueprint's field stages are `E` and `ℚ̄_ℓ`. Neither carries the six operations in the
repository (see `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`), so the field
statements are made for `ModuleCat Λ` with `[Field Λ]`: these are the statements for a finite
field `Λ = 𝔽_ℓ` of coefficients, the finite-field-coefficient form of Poincaré duality. The
statements are not specialised to finite `Λ`, so they also apply to any field stage that is
later realised as `ModuleCat Λ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Definitions

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- Untwisting a morphism `φ : Λ_T(m) ⟶ Λ_T` into a class of `Λ_T(-m)`:

`Λ_T ≅ Λ_T(m + (-m)) ≅ Λ_T(m) ⊗ᴸ Λ_T(-m) ⟶ Λ_T ⊗ᴸ Λ_T(-m) ≅ Λ_T(-m)`,

through the identifications `HasTateTwist.twistObjectZeroIso`,
`HasTateTwist.twistObjectAddIso` of the Tate twist datum and the left unitor. This is how a
trace or a pairing with values in `Λ` after a twist `(m)` is read as a `Λ(-m)`-valued one. -/
noncomputable def untwistTateObject (T : Scheme.{u}) (m : ℤ) :
    (tateObject Λ T m ⟶ 𝟙_ _) →ₗ[Λ] (𝟙_ _ ⟶ tateObject Λ T (-m)) where
  toFun φ := (HasTateTwist.twistObjectZeroIso T).inv ≫ eqToHom (by rw [add_neg_cancel]) ≫
    (HasTateTwist.twistObjectAddIso T m (-m)).inv ≫
      ((derivedTensor _ T).flip.obj (tateObject Λ T (-m))).map φ ≫
        (derivedTensorLeftUnitor _ T _).hom
  map_add' φ ψ := by
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r φ := by
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The composite of a pair of shifted morphisms `x : A ⟶ (Ra_! K)[i]`,
`y : B ⟶ (Ra_*(K^∨(d)))[j]`, `i + j = 2d`, with the derived Poincaré pairing:

`A ⊗ᴸ B ⟶ (Ra_! K)[i] ⊗ᴸ (Ra_*(K^∨(d)))[j] ≅ (Ra_! K ⊗ᴸ Ra_*(K^∨(d)))[2d]
  ≅ Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ⟶ Λ_s`.

For `A = B = Λ_s` it is the degreewise pairing of the classes `x` and `y`. -/
noncomputable def poincarePairingComp (a : X ⟶ Spec (CommRingCat.of k))
    [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (i j : ℤ) (hij : i + j = 2 * d)
    {A B : _root_.DerivedCategory
      (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (x : A ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : B ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((tateTwist Λ X d).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))))⟦j⟧) :
    ((derivedTensor _ _).obj A).obj B ⟶ 𝟙_ _ :=
  ((derivedTensor _ _).flip.obj B).map x ≫ ((derivedTensor _ _).obj _).map y ≫
    (derivedTensorShiftIso _ _ _ i j).hom ≫ eqToHom (by rw [hij]) ≫
      (poincarePairingShiftIso Λ a d K).inv ≫ poincarePairing Λ a d γ K

/-- The value `⟨x, y⟩ ∈ End (Λ_s)` of the degreewise Poincaré pairing at classes
`x ∈ H^i_c(X, K)` and `y ∈ H^j(X, K^∨(d))`, `i + j = 2d`: the composite
`Λ_s ≅ Λ_s ⊗ᴸ Λ_s ⟶ Λ_s` of the left unitor and
`AlgebraicGeometry.Etale.poincarePairingComp`. -/
noncomputable def degreewisePoincarePairingHom (a : X ⟶ Spec (CommRingCat.of k))
    [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : DerivedCategory.cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i)
    (y : DerivedCategory.cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((tateTwist Λ X d).obj ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj
        (op K)))) j) :
    End (𝟙_ (_root_.DerivedCategory
      (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :=
  (derivedTensorLeftUnitor _ _ _).inv ≫ poincarePairingComp Λ a d γ K i j hij x y

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

The *degreewise Poincaré pairing*

`⟨-,-⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`,

the `Λ`-bilinear form `AlgebraicGeometry.Etale.degreewisePoincarePairingHom` read in `Λ`
through `AlgebraicGeometry.Etale.coefficientRingEquiv`. Here `H^i_c(X, K)` and
`H^j(X, K^∨(d))` are the classes `Λ_s ⟶ (Ra_! K)[i]` and `Λ_s ⟶ (Ra_*(K^∨(d)))[j]` in
`D(s_ét, Λ)`. -/
noncomputable def degreewisePoincarePairing (a : X ⟶ Spec (CommRingCat.of k))
    [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (i j : ℤ) (hij : i + j = 2 * d) :
    DerivedCategory.cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i →ₗ[Λ]
      DerivedCategory.cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ X d).obj ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj
          (op K)))) j →ₗ[Λ] Λ :=
  (LinearMap.mk₂ Λ (degreewisePoincarePairingHom Λ a d γ K i j hij)
    (fun x x' y ↦ by
      simp only [degreewisePoincarePairingHom, poincarePairingComp, Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add])
    (fun r x y ↦ by
      simp only [degreewisePoincarePairingHom, poincarePairingComp, Functor.map_smul,
        Linear.smul_comp, Linear.comp_smul])
    (fun x y y' ↦ by
      simp only [degreewisePoincarePairingHom, poincarePairingComp, Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add])
    (fun r x y ↦ by
      simp only [degreewisePoincarePairingHom, poincarePairingComp, Functor.map_smul,
        Linear.smul_comp, Linear.comp_smul])).compr₂ (coefficientLinearMap Λ k)

/-- A class `y ∈ H^j(X, K^∨)` twisted into a morphism `Λ_s(d) ⟶ (Ra_*(K^∨(d)))[j]`:

`Λ_s(d) ≅ Λ_s ⊗ᴸ Λ_s(d) ⟶ (Ra_* K^∨)[j] ⊗ᴸ Λ_s(d) ≅ (Ra_* K^∨ ⊗ᴸ Λ_s(d))[j]
  ⟶ (Ra_*(K^∨ ⊗ᴸ La^* Λ_s(d)))[j] ≅ (Ra_*(K^∨(d)))[j]`,

through the projection map of `Ra_*` and `La^* Λ_s(d) ≅ Λ_X(d)`. -/
noncomputable def twistLowerStarClass (a : X ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (j : ℤ) :
    DerivedCategory.cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj M) j →ₗ[Λ]
      (tateObject Λ (Spec (CommRingCat.of k)) d ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((tateTwist Λ X d).obj M))⟦j⟧) where
  toFun y := (derivedTensorLeftUnitor _ _ _).inv ≫
    ((derivedTensor _ _).flip.obj (tateObject Λ (Spec (CommRingCat.of k)) d)).map y ≫
      (((derivedTensor _ _).flip.obj (tateObject Λ (Spec (CommRingCat.of k)) d)).commShiftIso
        j).hom.app _ ≫
      (((rightDerivedLowerStarProjectionMap _ a).app M).app _ ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map (((derivedTensor _ X).obj M).map
          (leftDerivedUpperStarTateObjectIso a d).hom))⟦j⟧'
  map_add' y y' := by
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r y := by
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

The *line-valued* form of the degreewise Poincaré pairing,

`H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`, `i + j = 2d`,

with values in the classes `Λ_s ⟶ Λ_s(-d)`: the class `y ∈ H^j(X, K^∨)` is twisted into
`Λ_s(d) ⟶ (Ra_*(K^∨(d)))[j]` (`AlgebraicGeometry.Etale.twistLowerStarClass`), paired with
`x` into `Λ_s(d) ⟶ Λ_s`, and the result untwisted
(`AlgebraicGeometry.Etale.untwistTateObject`). -/
noncomputable def untwistedDegreewisePoincarePairing (a : X ⟶ Spec (CommRingCat.of k))
    [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (i j : ℤ) (hij : i + j = 2 * d) :
    DerivedCategory.cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) i →ₗ[Λ]
      DerivedCategory.cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))) j →ₗ[Λ]
        (𝟙_ _ ⟶ tateObject Λ (Spec (CommRingCat.of k)) (-d)) :=
  LinearMap.mk₂ Λ (fun x y ↦ untwistTateObject Λ _ d ((derivedTensorLeftUnitor _ _ _).inv ≫
      poincarePairingComp Λ a d γ K i j hij x (twistLowerStarClass Λ a d _ j y)))
    (fun x x' y ↦ by
      simp only [poincarePairingComp, Functor.map_add, Preadditive.add_comp,
        Preadditive.comp_add, map_add])
    (fun r x y ↦ by
      simp only [poincarePairingComp, Functor.map_smul, Linear.smul_comp, Linear.comp_smul,
        map_smul])
    (fun x y y' ↦ by
      simp only [poincarePairingComp, map_add, Functor.map_add, Preadditive.add_comp,
        Preadditive.comp_add])
    (fun r x y ↦ by
      simp only [poincarePairingComp, map_smul, Functor.map_smul, Linear.smul_comp,
        Linear.comp_smul])

/-- The identification `H^i(X, M) ≅ H^i_c(X, M)` of ordinary and compactly supported classes
for a proper `a`, through `Ra_! ≅ Ra_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoLowerStar`). -/
noncomputable def lowerStarClassToLowerShriek (a : X ⟶ Spec (CommRingCat.of k)) [IsProper a]
    [HasCompactification a]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (i : ℤ) :
    DerivedCategory.cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj M) i →ₗ[Λ]
      DerivedCategory.cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj M) i :=
  Linear.rightComp Λ _ (((rightDerivedLowerShriekIsoLowerStar _ a).inv.app M)⟦i⟧')

end Definitions

section Statements

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]
  {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The derived pairing is perfect.** For `K` perfect over `Λ_X` and in `D^b_{ctf}(X, Λ)`, the
derived Poincaré pairing `β_K` is perfect: its tensor–internal-hom adjoint
`RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨` is an isomorphism. This is the content of
`sk-thm-sf-identification` (stated in
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation` as
the existence of that isomorphism), from which the degreewise form is read off. It needs no
field hypothesis. -/
theorem isPerfectPairing_poincarePairing [Finite Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K)
    (hKd : IsDualizable K) :
    DerivedCategory.IsPerfectPairing (poincarePairing Λ (S.structureMorphism k) d γ K) :=
  sorry

end Statements

section FieldStatements

variable (Λ : Type (u + 1)) [Field Λ] [HasTateTwist Λ]
  {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**Degreewise duality.** Over a field `Λ` of coefficients, for `K` perfect over `Λ_X` and in
`D^b_{ctf}(X, Λ)`, the degreewise Poincaré pairings

`⟨-,-⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`,

are perfect. -/
theorem isPerfPair_degreewisePoincarePairing [Finite Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K)
    (hKd : IsDualizable K) (i j : ℤ) (hij : i + j = 2 * d) :
    (degreewisePoincarePairing Λ (S.structureMorphism k) d γ K i j hij).IsPerfPair :=
  sorry

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The line-valued form.** Over a field `Λ` of coefficients, for `K` perfect over `Λ_X` and in
`D^b_{ctf}(X, Λ)`, the untwisted pairing `H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)` is perfect: both
of its adjoints, into the `Λ`-linear maps to the line `Λ(-d)`, are bijective. -/
theorem bijective_untwistedDegreewisePoincarePairing [Finite Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K)
    (hKd : IsDualizable K) (i j : ℤ) (hij : i + j = 2 * d) :
    Function.Bijective
        (untwistedDegreewisePoincarePairing Λ (S.structureMorphism k) d γ K i j hij) ∧
      Function.Bijective
        (untwistedDegreewisePoincarePairing Λ (S.structureMorphism k) d γ K i j hij).flip :=
  sorry

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

**The proper case.** For `X` proper, the same holds with `H_c` replaced by `H`: the pairing
`H^i(X, K) × H^j(X, K^∨(d)) ⟶ Λ`, obtained from `⟨-,-⟩_i` through the identification
`H^i(X, K) ≅ H^i_c(X, K)` of `Ra_* ≅ Ra_!`, is perfect. -/
theorem isPerfPair_degreewisePoincarePairing_of_isProper [Finite Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [IsProper (S.structureMorphism k)] [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K)
    (hKd : IsDualizable K) (i j : ℤ) (hij : i + j = 2 * d) :
    ((degreewisePoincarePairing Λ (S.structureMorphism k) d γ K i j hij).comp
      (lowerStarClassToLowerShriek Λ (S.structureMorphism k) K i)).IsPerfPair :=
  sorry

end FieldStatements

end Etale

end AlgebraicGeometry
