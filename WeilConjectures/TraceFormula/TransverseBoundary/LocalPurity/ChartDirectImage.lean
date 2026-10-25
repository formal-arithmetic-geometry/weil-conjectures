/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleAffineLimitBaseChange

/-!
# Direct images from the complement of a divisor on a limit of étale schemes

Let `W` be an affine scheme smooth over an algebraically closed field `k` and `π : O ⟶ W` a limit
of affine étale schemes over `W` (`AlgebraicGeometry.Scheme.Hom.IsEtaleAffineLimit`). Let `g` be
a function on `W` which, at the image `π y` of a point `y` of `O`, lies in the maximal ideal of
the (regular) local ring but not in its square, so that `V(g)` is a regular divisor of `W` near
`π y`. Then near `y`, writing `j : O - π⁻¹V(g) ⟶ O`,

`R⁰j_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j_* ℤ/ℓ ≅ i'_* ℤ/ℓ` and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`,

for a closed immersion `i'` with support `π⁻¹V(g)` (blueprint `det-tf-transverse-corner-constant`).
This is purity on `W` (`AlgebraicGeometry.Etale.exists_higherDirectImage_of_isRegularImmersion`)
transported along `π`
(`Etale.nonempty_iso_upperStar_higherDirectImage_of_isEtaleAffineLimit`,
`Etale.nonempty_iso_upperStar_lowerStar_constantZModModule_of_isPullback`).

## Main statements

- `AlgebraicGeometry.Etale.exists_higherDirectImage_of_isEtaleAffineLimit`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- **Direct images from the complement of a divisor on a limit of étale schemes.** Let `W` be
affine and smooth over an algebraically closed field `k`, `π : O ⟶ W` a limit of affine étale
schemes and `g` a function on `W` whose germ at `π y` lies in `𝔪 \ 𝔪²`. There are an open
neighbourhood `O'` of `y` and a closed immersion `i' : D' ⟶ O'` with support `π⁻¹V(g) ∩ O'` such
that, for the open immersion `j' : π⁻¹D(g) ∩ O' ⟶ O'`,

`R⁰j'_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j'_* ℤ/ℓ ≅ i'_* ℤ/ℓ` and `R^q j'_* ℤ/ℓ = 0` for `q ≥ 2`. -/
theorem exists_higherDirectImage_of_isEtaleAffineLimit {k : Type u} [Field k] [IsAlgClosed k]
    {W O : Scheme.{u}} [IsAffine W] (aW : W ⟶ Spec (.of k)) [Smooth aW] (π : O ⟶ W)
    (hπ : π.IsEtaleAffineLimit) (g : Γ(W, ⊤)) (y : O)
    (hg : W.presheaf.germ ⊤ (π y) trivial g ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk (π y)))
    (hg2 : W.presheaf.germ ⊤ (π y) trivial g ∉
      IsLocalRing.maximalIdeal (W.presheaf.stalk (π y)) ^ 2)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    ∃ (O' : O.Opens) (_ : y ∈ O') (D' : Scheme.{u}) (i' : D' ⟶ O') (_ : IsClosedImmersion i')
      (_ : Set.range (i' ≫ O'.ι) = π ⁻¹' (W.basicOpen g : Set W)ᶜ ∩ (O' : Set O)),
      (∀ q : ℕ, 2 ≤ q → IsZero (higherDirectImage (ZModCoeff.{u} ℓ)
        (pullback.snd (π ⁻¹ᵁ W.basicOpen g).ι O'.ι) q (constantZModModule _ ℓ))) ∧
      Nonempty (higherDirectImage (ZModCoeff.{u} ℓ) (pullback.snd (π ⁻¹ᵁ W.basicOpen g).ι O'.ι) 0
        (constantZModModule _ ℓ) ≅ constantZModModule O' ℓ) ∧
      Nonempty (higherDirectImage (ZModCoeff.{u} ℓ) (pullback.snd (π ⁻¹ᵁ W.basicOpen g).ι O'.ι) 1
        (constantZModModule _ ℓ) ≅
          (i')_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D' ℓ)) := by
  sorry

end AlgebraicGeometry.Etale
