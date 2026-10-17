/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# Dual base change for the exceptional inverse image

For a cartesian square of schemes
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
with `f`, `f'` admitting compactifications and torsion coefficients `Λ`, the compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). The composite
`Lg^* Rf_!` has the right adjoint `Rf^! Rg_*`, and `Rf'_! Lg'^*` has the right adjoint
`Rg'_* Rf'^!`; the conjugate of `Ex_!⁻¹` under these composite adjunctions is the
*dual base change map*
```
  β^∨ : Rf^! Rg_* ⟶ Rg'_* Rf'^!,
```
which is an isomorphism, the conjugate of an isomorphism (blueprint
`prop-exc-ambient-dual-base-change`). Here the right adjoint `Rf^!` of `Rf_!` exists
unconditionally (`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`), so the
ambient exceptional right adjoint datum of the blueprint is automatic.

The pro-étale analogue is not stated: the pro-étale compact-support base change
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekBaseChangeMap` is only known to be invertible
on complexes of étale origin, not as a natural transformation of functors on the ambient
derived categories, so its conjugate is not known to be invertible.

## Main definitions and statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualBaseChangeMap`: `β^∨`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekDualBaseChangeMap`: `β^∨` is an
  isomorphism.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualBaseChangeIso`: `β^∨` as an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- The **dual base change map** `β^∨ : Rf^! Rg_* ⟶ Rg'_* Rf'^!` of a cartesian square
`g' ≫ f = f' ≫ g`, for torsion coefficients: the conjugate, under the composite adjunctions
`Lg^* Rf_! ⊣ Rf^! Rg_*` and `Rf'_! Lg'^* ⊣ Rg'_* Rf'^!`, of the inverse of the compact-support
base change isomorphism `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). In the diagrammatic
order of composition of functors used here, it is `Rg_* ⋙ Rf^! ⟶ Rf'^! ⋙ Rg'_*`. -/
noncomputable def rightDerivedUpperShriekDualBaseChangeMap (sq : IsPullback g' f' f g) :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![ModuleCat.{u + 1} Λ] ⟶
      R(f')^![ModuleCat.{u + 1} Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  conjugateEquiv
    ((rightDerivedUpperShriekAdjunction _ f).comp (derivedUpperStarLowerStarAdjunction _ g))
    ((derivedUpperStarLowerStarAdjunction _ g').comp (rightDerivedUpperShriekAdjunction _ f'))
    (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))

/-- Blueprint `prop-exc-ambient-dual-base-change`: Dual base change for the ambient right
adjoint is formal.

For a cartesian square `g' ≫ f = f' ≫ g` with `f`, `f'` admitting compactifications (and `f'`
quasi-compact) and `g` arbitrary, and torsion coefficients `Λ`, the right-adjoint mate
`β^∨ : Rf^! Rg_* ⟶ Rg'_* Rf'^!` of the compact-support base change isomorphism is an
isomorphism: an isomorphism of left adjoints induces an isomorphism of their right adjoints
(`CategoryTheory.conjugateEquiv_iso`). The ambient right adjoints `Rf^!`, `Rf'^!` exist for
torsion coefficients (`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`). -/
instance isIso_rightDerivedUpperShriekDualBaseChangeMap (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedUpperShriekDualBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  unfold rightDerivedUpperShriekDualBaseChangeMap
  infer_instance

/-- The dual base change isomorphism `Rf^! Rg_* ≅ Rg'_* Rf'^!` of a cartesian square, for
torsion coefficients (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekDualBaseChangeMap`).
-/
noncomputable def rightDerivedUpperShriekDualBaseChangeIso (sq : IsPullback g' f' f g) :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![ModuleCat.{u + 1} Λ] ≅
      R(f')^![ModuleCat.{u + 1} Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]) :=
  asIso (rightDerivedUpperShriekDualBaseChangeMap Λ sq)

end Etale

end AlgebraicGeometry
