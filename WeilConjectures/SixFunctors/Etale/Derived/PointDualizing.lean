/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# The dualizing complex of the identity

For a finite coefficient ring `Λ` and a scheme `S`, the compactly supported direct image along
the identity `𝟙 S` is the identity functor, hence so is its right adjoint, the exceptional
inverse image. Consequently the dualizing complex of `𝟙 S` is the constant complex `Λ_S`, and the
Verdier dual `𝔻_S = RHom(-, ω_S)` relative to `𝟙 S` is the coefficient dual `(-)^∨ = RHom(-, Λ_S)`.
For `S = s` the geometric point this is blueprint `lem-pod-point-dualizing-complex`; the proof
does not use anything about `S`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`: `R(𝟙 S)_! ≅ 𝟭`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`: `R(𝟙 S)^! ≅ 𝟭`.
- `AlgebraicGeometry.Etale.dualizingComplexIdIso` (`lem-pod-point-dualizing-complex`):
  `ω_S = R(𝟙 S)^! Λ_S ≅ Λ_S`.
- `AlgebraicGeometry.Etale.verdierDualIdIso` (`lem-pod-point-dualizing-complex`):
  `𝔻_S ≅ (-)^∨`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (S : Scheme.{u})

/-- The compactly supported direct image along an identity is the identity:
`R(𝟙 S)_! ≅ R(𝟙 S)_* ≅ 𝟭`, the identity being proper
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
noncomputable def rightDerivedLowerShriekIdIso :
    R(𝟙 S)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar _ (𝟙 S) ≪≫ rightDerivedLowerStarIdIso Λ S

/-- The exceptional inverse image along an identity is the identity, `R(𝟙 S)^! ≅ 𝟭`: it is right
adjoint to `R(𝟙 S)_! ≅ 𝟭`, and right adjoints are unique. -/
noncomputable def rightDerivedUpperShriekIdIso :
    R(𝟙 S)^![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
  ((rightDerivedUpperShriekAdjunction _ (𝟙 S)).ofNatIsoLeft
    (rightDerivedLowerShriekIdIso Λ S)).rightAdjointUniq Adjunction.id

/-- Blueprint `lem-pod-point-dualizing-complex`: Dualizing complex of the point.

The dualizing complex of the identity of `S` is the constant complex:
`ω_S = R(𝟙 S)^! Λ_S ≅ Λ_S`. -/
noncomputable def dualizingComplexIdIso :
    dualizingComplex (ModuleCat.{u + 1} Λ) (𝟙 S) ≅ 𝟙_ _ :=
  (rightDerivedUpperShriekIdIso Λ S).app _

/-- Blueprint `lem-pod-point-dualizing-complex`: Dualizing complex of the point.

The Verdier dual relative to the identity of `S` is the coefficient dual:
`𝔻_S C = RHom(C, ω_S) ≅ RHom(C, Λ_S) = C^∨`, naturally in `C`. -/
noncomputable def verdierDualIdIso :
    verdierDual (ModuleCat.{u + 1} Λ) (𝟙 S) ≅
      DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S :=
  (RHom(S)[ModuleCat.{u + 1} Λ]).flip.mapIso ((rightDerivedUpperShriekIdIso Λ S).app _)

end Etale

end AlgebraicGeometry
