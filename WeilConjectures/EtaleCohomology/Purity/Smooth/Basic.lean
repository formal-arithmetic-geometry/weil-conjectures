/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# Cohomological smoothness and finite-coefficient smooth purity

The two central statements of the block. For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and a finite coefficient ring `Λ` whose exponent is invertible on `X`:

* *cohomological smoothness* (`sk-prop-cohsm`): the dualizing complex `ω_f = Rf^! Λ_Y` is
  ⊗-invertible, `Rf^! K ≅ Lf^* K ⊗^L ω_f` for every `K ∈ D^b_{ctf}(Y, Λ)`, and the formation
  of `Rf^!` commutes with base change;
* *smooth purity* (`sk-thm-smooth-purity`): `ω_f ≅ Λ_X(d)[2d]`, hence
  `Rf^! K ≅ Lf^* K(d)[2d]`.

The route is the blueprint's: the model case is the `Rπ^!`-form of `𝔸ⁿ`-purity,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`, transported
along the deformation to the normal cone of the diagonal, which is a regular immersion of
codimension `d` by `AlgebraicGeometry.isRegularImmersion_diagonal`.

## Implementation notes

Clauses (b) and (c) of `sk-prop-cohsm` are stated as `IsIso` of the canonical maps
`AlgebraicGeometry.Etale.tensorFormulaMap` and
`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChange`. Both are mates of maps whose
inverses are needed (the projection map and the compact-support exchange), so they are defined
from the theorems making those maps invertible, with the hypotheses of those theorems.

The smooth-purity isomorphism of `sk-thm-smooth-purity`, and the additivity of the dualizing
complex under composition, are still stated as existence of an isomorphism: their canonical
forms need the composition isomorphism of `Rf_!`, which is not constructed.

## Main definitions

- `AlgebraicGeometry.Etale.tensorFormulaMap`: `φ_K : ω_f ⊗^L Lf^* K ⟶ Rf^! K`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChange`: `Lg'^* Rf^! ⟶ Rf'^! Lg^*`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_dualizingComplex`
- `AlgebraicGeometry.Etale.boundedConstructible_dualizingComplex`
- `AlgebraicGeometry.Etale.isIso_tensorFormulaMap`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChange`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Aux

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
  [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The tensor-formula map `AlgebraicGeometry.Etale.tensorFormulaMap`, for a general coefficient
category `A`. It is stated for a variable `A` so that the monoidal structure of the derived
category (in `𝟙_` and `λ_`) is never unfolded at `A = ModuleCat Λ`, where the kernel cannot
check it in reasonable time (compare `DerivedCategory.εSingleFunctorZero`). -/
noncomputable def tensorFormulaMapAux
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    [hPF : IsIso (((projectionMap A f).app (dualizingComplex A f)).app K)] :
    ((derivedTensor A X).obj (dualizingComplex A f)).obj ((L((f)^*[A])).obj K) ⟶
      (rightDerivedUpperShriek A f).obj K :=
  ((rightDerivedUpperShriekAdjunction A f).homEquiv _ _)
    (@inv _ _ _ _ (((projectionMap A f).app (dualizingComplex A f)).app K) hPF ≫
      ((derivedTensor A Y).map ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))).app K ≫
      (λ_ K).hom)

end Aux

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [hf : SmoothOfRelativeDimension d f] [HasCompactification f]
  [HasInvertibleExponent Λ X]

include hf in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (a).* For `f` smooth separated of pure relative dimension `d` the dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible: it is a lisse rank-one object, twisted and shifted. This is
the form of cohomological smoothness that does not yet name the twist; smooth purity
identifies `ω_f` with `Λ_X(d)[2d]`. -/
theorem isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) f) :=
  sorry

include hf in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

For `f` smooth separated, the dualizing complex `ω_f` is bounded with constructible cohomology
sheaves: by clause (a) it is a lisse rank-one sheaf placed in one degree. This is what lets the
projection formula, and with it the tensor formula of clause (b), be applied with `ω_f` as the
first argument. -/
theorem boundedConstructible_dualizingComplex :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (dualizingComplex (ModuleCat.{u + 1} Λ) f) :=
  sorry

/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

The *tensor-formula map* `φ_K : ω_f ⊗^L Lf^* K ⟶ Rf^! K`, the mate of the projection formula: the
transpose under `Rf_! ⊣ Rf^!` of

`Rf_!(ω_f ⊗^L Lf^* K) ≅ Rf_! ω_f ⊗^L K ⟶ Λ_Y ⊗^L K ≅ K`,

the inverse of the projection map `PF` at `(ω_f, K)`, then the counit
`Rf_! ω_f = Rf_! Rf^! Λ_Y ⟶ Λ_Y`, then the left unitor. It is defined whenever that projection
map is invertible, which is the case for `K ∈ D^b_{ctf}(Y, Λ)`
(`AlgebraicGeometry.Etale.isIso_tensorFormulaMap`). -/
noncomputable def tensorFormulaMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app
      (dualizingComplex (ModuleCat.{u + 1} Λ) f)).app K)] :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  tensorFormulaMapAux (ModuleCat.{u + 1} Λ) f K

include hf in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (b), the tensor formula.* For `f` smooth separated of pure relative dimension `d` and
`K ∈ D^b_{ctf}(Y, Λ)`, the tensor-formula map

`φ_K : ω_f ⊗^L Lf^* K ⟶ Rf^! K`

is an isomorphism. Equivalently, `Rf^!` is `Lf^*` twisted by the invertible object `ω_f` of
clause (a); this is what turns the computation of `ω_f` into a computation of `Rf^!` on all
coefficients. The projection map at `(ω_f, K)` that `φ_K` is built from is invertible by
`AlgebraicGeometry.Etale.isIso_projectionMap_app_app`, which needs the exponent of `Λ` to be
invertible on `Y`. -/
theorem isIso_tensorFormulaMap [HasInvertibleExponent Λ Y] [LocallyOfFiniteType f]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    haveI := isIso_projectionMap_app_app Λ f _ K
      (boundedConstructible_dualizingComplex Λ f (d := d)) hK
    IsIso (tensorFormulaMap Λ f K) :=
  sorry

/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

The *base-change map for `R^!`* of a cartesian square `g' ≫ f = f' ≫ g`,

`Lg'^* Rf^! ⟶ Rf'^! Lg^*`,

the mate under `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!` of the inverse of the compact-support exchange
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`),
which is invertible by compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). On `K` it is the transpose
of `Rf'_! Lg'^* Rf^! K ≅ Lg^* Rf_! Rf^! K ⟶ Lg^* K`. -/
noncomputable def rightDerivedUpperShriekBaseChange {X' Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [HasCompactification f']
    [QuasiCompact f'] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f' :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  mateEquiv (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f')
    (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))

include hf in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (c), smooth base change for `R^!`.* In the cartesian square

```
  X' --g'--> X          Rf^! ⋙ Lg'^*  ⟶  Lg^* ⋙ Rf'^!
  |          |
  f'         f          as functors D(Y_ét, Λ) ⥤ D(X'_ét, Λ)
  |          |
  v          v
  Y' --g---> Y
```

with `f` smooth and `f'` its base change along `g`, the formation of `Rf^!` commutes with base
change: the base-change map `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChange` is an
isomorphism. Applied to the diagonal square `W = X ×_Y X` this gives `ω_{p₁} ≅ Lp₂^* ω_f` and
`ω_{p₂} ≅ Lp₁^* ω_f`, which is what makes the diagonal computation of the purity theorem
possible. -/
theorem isIso_rightDerivedUpperShriekBaseChange {X' Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [HasCompactification f']
    [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChange Λ f sq) :=
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
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  sorry

end Etale

end AlgebraicGeometry
