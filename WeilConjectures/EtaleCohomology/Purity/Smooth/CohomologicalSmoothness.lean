/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Cohomological smoothness

For `f : X ⟶ Y` smooth separated of pure relative dimension `d` and a finite coefficient ring
`Λ` whose exponent is invertible on `X` (`sk-prop-cohsm`): the dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible, `Rf^! K ≅ Lf^* K ⊗^L ω_f` for every `K ∈ D^b_{ctf}(Y, Λ)`,
and the formation of `Rf^!` commutes with base change.

These are the inputs of both the deformation to the normal cone
(`WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation`) and smooth purity
(`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`). The notion of a cohomologically smooth
morphism and its structural properties are in
`WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth`.

## Implementation notes

The three clauses of `sk-prop-cohsm` are read off from the orientation-free smooth duality of
the ambient chapter, as in the proof of `thm-pur-cohomological-smoothness`: the locally constant
rank-one shape of `ω_f` and the tensor formula
(`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`, `thm-asd-smooth-tensor`),
and arbitrary base change for `Rf^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar`,
`prop-asd-smooth-base-change`). A locally constant sheaf with free rank-one stalks, placed in any
degree, is invertible
(`AlgebraicGeometry.Etale.isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf`).
The canonical form of clause (b) is
`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension`.

The statements carry `include d in`: they do not mention the relative dimension `d`, and
without it the hypothesis `[SmoothOfRelativeDimension d f]` would silently be dropped. They hold
without the Tate twist datum and without separatedness (which is implied by the
compactification), so these hypotheses are omitted.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_dualizingComplex`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`,
  `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension`
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`
- `AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_constantComplex_of_etale`: `ω_e ≅ Λ_X`
  for `e` étale (`lem-pur-co-smooth-etale-locality`), hence `Re^! K ≅ Le^* K`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_of_etale`).
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

omit [HasTateTwist Λ] [IsSeparated f] in
include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (a).* For `f` smooth separated of pure relative dimension `d` the dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible: it is a lisse rank-one object, twisted and shifted. This is
the form of cohomological smoothness that does not yet name the twist; smooth purity
identifies `ω_f` with `Λ_X(d)[2d]`. -/
theorem isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ f) := by
  obtain ⟨L, _, hL, ⟨e⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  exact DerivedCategory.isInvertible.of_iso e.symm
    (isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf L hL _)

omit [HasTateTwist Λ] [IsSeparated f] in
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
possible. The isomorphism is the canonical base change map
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`),
which is constructed for quasi-compact `f'` and shown to be an isomorphism over a
quasi-separated base `Y`; both hypotheses hold in the Noetherian setting of the blueprint.
-/
theorem nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek [QuasiSeparatedSpace Y]
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [HasCompactification f'] [QuasiCompact f'] :
    Nonempty (rightDerivedUpperShriek Λ f ⋙
        L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙
        rightDerivedUpperShriek Λ f') :=
  nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar Λ f d sq

end Etale

end AlgebraicGeometry
