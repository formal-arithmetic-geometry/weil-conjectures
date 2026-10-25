/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TransverseBoundary.Basic
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# Direct images from the complement of a regular divisor of an étale limit of surfaces

Let `Z` be an étale limit with affine transition maps of smooth surfaces over an algebraically
closed field `k` (`AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`), `i : D ⟶ Z` a regular
divisor with `D` regular and `j : U ⟶ Z` its open complement. For a prime `ℓ` invertible in `k`,
every point `y` of `D` has an open neighbourhood `O` in `Z` over which

`R⁰j_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j_* ℤ/ℓ ≅ i'_* ℤ/ℓ` and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`,

for a closed immersion `i' : D' ⟶ O` with the same support as `D ∩ O` (blueprint
`det-tf-transverse-corner-constant`, *the surface*).

*Local chart.* A local equation of `D` at `y`, on an affine open neighbourhood of `y`, comes from
a function `t` on an affine open `W` of some stage `Z_i` of the limit, and `V(t) ⊆ W` is a
regular divisor near the image of `y` (its local ring maps to the regular local ring of `D` at
`y`, and `t` is not in the square of the maximal ideal). The open `O ⊆ Z` is the inverse image
of `W`, the limit of the inverse images of `W` in the later stages, which are étale over `W`.
Purity on the smooth surface `W`
(`AlgebraicGeometry.Etale.exists_higherDirectImage_of_isRegularImmersion`) computes the direct
images on `W`, and they pull back to `O` by base change along the limit of étale maps
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_higherDirectImage_of_isEtaleLimitOfSmoothSurfaces`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Etale

/-- **Direct images from the complement of a regular divisor** (blueprint
`det-tf-transverse-corner-constant`, *the surface*). Let `Z` be an étale limit of smooth
surfaces over an algebraically closed field `k`, `i : D ⟶ Z` a regular divisor with `D`
regular and `j : U ⟶ Z` its open complement. Every point `y` of `D` has an open neighbourhood
`O` with a closed immersion `i' : D' ⟶ O` of support `D ∩ O` such that, for
`j_O : U ∩ O ⟶ O`,

`R⁰j_{O*} ℤ/ℓ ≅ ℤ/ℓ`, `R¹j_{O*} ℤ/ℓ ≅ i'_* ℤ/ℓ` and `R^q j_{O*} ℤ/ℓ = 0` for `q ≥ 2`. -/
theorem exists_higherDirectImage_of_isEtaleLimitOfSmoothSurfaces {k : Type u} [Field k]
    [IsAlgClosed k] {Z D U : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
    (hZ : IsEtaleLimitOfSmoothSurfaces aZ) [IsLocallyNoetherian Z] (iD : D ⟶ Z)
    [IsRegular Z] [IsRegularImmersion 1 iD] [IsRegular D] (j : U ⟶ Z) [IsOpenImmersion j]
    (hj : Set.range j = (Set.range iD)ᶜ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (y : Z)
    (hy : y ∈ Set.range iD) :
    ∃ (O : Z.Opens) (_ : y ∈ O) (D' : Scheme.{u}) (i' : D' ⟶ O) (_ : IsClosedImmersion i')
      (_ : Set.range (i' ≫ O.ι) = Set.range iD ∩ (O : Set Z)),
      (∀ q : ℕ, 2 ≤ q → IsZero (higherDirectImage (ZModCoeff.{u} ℓ)
        (pullback.snd j O.ι) q (constantZModModule _ ℓ))) ∧
      Nonempty (higherDirectImage (ZModCoeff.{u} ℓ) (pullback.snd j O.ι) 0
        (constantZModModule _ ℓ) ≅ constantZModModule O ℓ) ∧
      Nonempty (higherDirectImage (ZModCoeff.{u} ℓ) (pullback.snd j O.ι) 1
        (constantZModModule _ ℓ) ≅
          (i')_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D' ℓ)) := by
  sorry

end AlgebraicGeometry.Scheme
