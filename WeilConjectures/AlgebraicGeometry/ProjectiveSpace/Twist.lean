/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist

/-!
# The twisting sheaves `𝒪(m)` on projective space

The projective space `ℙ(n; S)` is the base change to `S` of the integral model
`Proj.projectiveSpaceOverAffine n (ULift ℤ) = Proj ℤ[Tᵢ]`, and `ProjectiveSpace.toProjInt` is
the projection to it. The twisting sheaf `𝒪(m)` on `ℙ(n; S)` is the pullback along this
projection of the twisting sheaf `Proj.twist` of the integral model.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twist`: the twisting sheaf `𝒪(m)` on `ℙ(n; S)`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.twistZeroIsoUnit`: `𝒪(0)` is the structure sheaf.
- `AlgebraicGeometry.ProjectiveSpace.isInvertible_twist`: `𝒪(m)` is invertible when there are
  finitely many homogeneous coordinates.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- **The twisting sheaf `𝒪(m)` on `ℙ(n; S)`**: the pullback along the projection
`ℙ(n; S) ⟶ Proj ℤ[Tᵢ]` of the twisting sheaf `𝒪(m)` of the integral model. -/
def twist (m : ℤ) : (ℙ(n; S)).Modules :=
  (Scheme.Modules.pullback (toProjInt n S)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) m)

/-- **`𝒪(0)` is the structure sheaf** of `ℙ(n; S)`. -/
def twistZeroIsoUnit : twist n S 0 ≅ SheafOfModules.unit (ℙ(n; S)).ringCatSheaf :=
  (Scheme.Modules.pullback (toProjInt n S)).mapIso Proj.unitIsoTwistZero.symm ≪≫
    Scheme.Modules.pullbackObjUnitIso (toProjInt n S)

/-- **`𝒪(m)` is invertible** on `ℙ(n; S)` when there are finitely many homogeneous
coordinates. -/
instance isInvertible_twist [Finite n] (m : ℤ) : (twist n S m).IsInvertible :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
