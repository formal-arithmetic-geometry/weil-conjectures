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
dimension `d` and a finite coefficient ring `Λ` whose exponent is invertible on `X`:

* *cohomological smoothness* (`sk-prop-cohsm`): the dualizing complex `ω_f = Rf^! Λ_Y` is
  ⊗-invertible, `Rf^! K ≅ Lf^* K ⊗^L ω_f` for every `K ∈ D^b_{ctf}(Y, Λ)`, and the formation
  of `Rf^!` commutes with base change;
* *smooth purity* (`sk-thm-smooth-purity`): `ω_f ≅ Λ_X(d)[2d]`, hence
  `Rf^! K ≅ Lf^* K(d)[2d]`.

The route is the blueprint's: the model case is the `𝔸ⁿ`-purity of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero`, transported
along the deformation to the normal cone of the diagonal, which is a regular immersion of
codimension `d` by `AlgebraicGeometry.isRegularImmersion_diagonal`.

## Implementation notes

The blueprint asserts that each isomorphism below is *canonical*: `sk-prop-cohsm` (b) is about
the mate `φ_K : Lf^* K ⊗ ω_f ⟶ Rf^! K` of the projection formula, and `sk-thm-smooth-purity`
about the normalized comparison. Neither map exists in the repository — the projection map
itself is a TODO of `WeilConjectures.SixFunctors.Etale.Derived.Exchange` — so each statement
records the existence of the isomorphism only, with a `TODO(unify)` marker.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_dualizingComplex`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [HasInvertibleExponent Λ X]

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (a).* For `f` smooth separated of pure relative dimension `d` the dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible: it is a lisse rank-one object, twisted and shifted. This is
the form of cohomological smoothness that does not yet name the twist; smooth purity
identifies `ω_f` with `Λ_X(d)[2d]`. -/
theorem isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) f) :=
  sorry

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (b), the tensor formula.* For `f` smooth separated of pure relative dimension `d` and
`K ∈ D^b_{ctf}(Y, Λ)`,

`Rf^! K ≅ Lf^* K ⊗^L ω_f`.

Equivalently, `Rf^!` is `Lf^*` twisted by the invertible object `ω_f` of clause (a); this is
what turns the computation of `ω_f` into a computation of `Rf^!` on all coefficients. The
blueprint statement is that the mate `φ_K` of the projection formula is this isomorphism. -/
-- TODO(unify): sk-prop-cohsm — state `IsIso φ_K` once the projection map is available.
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) :=
  sorry

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (c), smooth base change for `R^!`.* In the cartesian square

```
  X' --g'--> X          Rf^! ⋙ Lg'^*  ≅  Lg^* ⋙ Rf'^!
  |          |
  f'         f          as functors D(Y_ét, Λ) ⥤ D(X'_ét, Λ)
  |          |
  v          v
  Y' --g---> Y
```

with `f` smooth and `f'` its base change along `g`, the formation of `Rf^!` commutes with base
change. Applied to the diagonal square `W = X ×_Y X` this gives `ω_{p₁} ≅ Lp₂^* ω_f` and
`ω_{p₂} ≅ Lp₁^* ω_f`, which is what makes the diagonal computation of the purity theorem
possible. -/
theorem nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek {X' Y' : Scheme.{u}}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] :
    Nonempty (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f ⋙
        L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙
        rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f') :=
  sorry

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Additivity of the dualizing complex under composition.** For composable smooth separated
morphisms `g : W ⟶ X` and `f : X ⟶ Y`,

`ω_{g ≫ f} ≅ ω_g ⊗^L Lg^* ω_f`,

which is the multiplicativity of the twist that `sk-thm-regular` divides one dualizing complex
into another with. It is the mate of the composition law `R(g ≫ f)^! ≅ Rf^! ⋙ Rg^!` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp` applied to `Λ_Y`. -/
theorem nonempty_iso_dualizingComplex_comp {W : Scheme.{u}} {e : ℕ} (g : W ⟶ X)
    [IsSeparated g] [SmoothOfRelativeDimension e g] [HasCompactification g]
    [HasCompactification (g ≫ f)] [HasInvertibleExponent Λ W] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (g ≫ f) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) g)).obj
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f))) :=
  sorry

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Smooth purity, finite coefficients.** For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and a finite coefficient ring `Λ` whose exponent is invertible on `X`,

`ω_f = Rf^! Λ_Y ≅ Λ_X(d)[2d]`,

canonically, compatibly with base change and additively in the twist under composition of
smooth morphisms.

The proof is the blueprint's five moves: the rank-one computation on `𝔸¹`
(`sk-prop-a1-kummer`, `sk-prop-a1`), its Künneth iteration to `𝔸ⁿ` (`sk-prop-an`), the
deformation to the normal cone of a section (`sk-lem-geometry`, `sk-thm-dnc`), the regularity
of the diagonal (`sk-lem-diag-reg`), and `𝔸¹`-invariance (`sk-prop-a1-inv`). -/
theorem nonempty_iso_dualizingComplex_twistShift :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :=
  sorry

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**The purity isomorphism on all coefficients.** Combining the tensor formula of
`sk-prop-cohsm` (b) with `ω_f ≅ Λ_X(d)[2d]`: for `f` smooth separated of pure relative
dimension `d` and every `K ∈ D^b_{ctf}(Y, Λ)`,

`Rf^! K ≅ (Lf^* K)(d)[2d]`. -/
theorem nonempty_iso_rightDerivedUpperShriek_twistShift
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  sorry

end Etale

end AlgebraicGeometry
