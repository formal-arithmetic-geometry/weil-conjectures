/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine

/-!
# Cohomological smoothness and finite-coefficient smooth purity

The two central statements of the block. For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and finite coefficients `Λ`:

* *cohomological smoothness* (`sk-prop-cohsm`): the dualizing complex `ω_f = Rf^! Λ_Y` is
  ⊗-invertible, `Rf^! K ≅ Lf^* K ⊗^L ω_f` for every `K`, and the formation of `Rf^!` commutes
  with base change;
* *smooth purity* (`sk-thm-smooth-purity`): `ω_f ≅ Λ_X(d)[2d]`, hence
  `Rf^! K ≅ Lf^* K(d)[2d]`.

The route is the blueprint's: the model case is the `𝔸ⁿ`-purity of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero`, transported
along the deformation to the normal cone of the diagonal, which is a regular immersion of
codimension `d` by `AlgebraicGeometry.isRegularImmersion_diagonal`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_dualizingComplex`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`
- `AlgebraicGeometry.Etale.nonempty_iso_upperStar_comp_rightDerivedUpperShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
  (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]

/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (a).* For `f` smooth separated of pure relative dimension `d` the dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible: it is a lisse rank-one object, twisted and shifted. This is
the form of cohomological smoothness that does not yet name the twist; smooth purity
identifies `ω_f` with `Λ_X(d)[2d]`. -/
theorem isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ f) :=
  sorry

/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (b), the tensor formula.* For `f` smooth separated of pure relative dimension `d` and
any `K ∈ D(Y_ét, Λ)`,

`Rf^! K ≅ Lf^* K ⊗^L ω_f`.

Equivalently, `Rf^!` is `Lf^*` twisted by the invertible object `ω_f` of clause (a); this is
what turns the computation of `ω_f` into a computation of `Rf^!` on all coefficients. -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj (dualizingComplex Λ f) ≅
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) :=
  sorry

/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (c), smooth base change for `R^!`.* In a cartesian square with `f` smooth and `f'` its
base change along `g`, the formation of `Rf^!` commutes with base change:

`Lg'^* ∘ Rf^! ≅ Rf'^! ∘ Lg^*`.

Applied to the diagonal square `W = X ×_Y X` this gives `ω_{p₁} ≅ Lp₂^* ω_f` and
`ω_{p₂} ≅ Lp₁^* ω_f`, which is what makes the diagonal computation of the next theorem
possible. -/
theorem nonempty_iso_upperStar_comp_rightDerivedUpperShriek {X' Y' : Scheme.{u}}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (_sq : IsPullback g' f' f g)
    [HasCompactification f'] :
    Nonempty (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f ⋙
        L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙
        Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f') :=
  sorry

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Smooth purity, finite coefficients.** For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and a finite coefficient ring `Λ`,

`ω_f = Rf^! Λ_Y ≅ Λ_X(d)[2d]`,

canonically, compatibly with base change and additively in the twist under composition of
smooth morphisms.

The proof is the blueprint's five moves: the rank-one computation on `𝔸¹`
(`sk-prop-a1-kummer`, `sk-prop-a1`), its Künneth iteration to `𝔸ⁿ` (`sk-prop-an`), the
deformation to the normal cone of a section (`sk-lem-geometry`, `sk-thm-dnc`), the regularity
of the diagonal (`sk-lem-diag-reg`), and `𝔸¹`-invariance (`sk-prop-a1-inv`). -/
theorem nonempty_iso_dualizingComplex_twistShift :
    Nonempty (dualizingComplex Λ f ≅ (twistShift Λ X d).obj (constantComplex Λ X)) :=
  sorry

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**The purity isomorphism on all coefficients.** Combining the tensor formula of
`sk-prop-cohsm` (b) with `ω_f ≅ Λ_X(d)[2d]`: for `f` smooth separated of pure relative
dimension `d` and every `K ∈ D(Y_ét, Λ)`,

`Rf^! K ≅ (Lf^* K)(d)[2d]`. -/
theorem nonempty_iso_rightDerivedUpperShriek_twistShift
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  sorry

end Etale

end AlgebraicGeometry
