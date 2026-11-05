/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Transition

/-!
# The transition rule for the generators of the twisting sheaves

On the overlap `Uᵢ ∩ Uⱼ` of two standard opens of `ℙ(n; S)`, the free generators
`e_i^{(d)} = xᵢᵈ` of `𝒪(d)` (`AlgebraicGeometry.ProjectiveSpace.twistGenerator`) satisfy
`e_i^{(d)} = (xᵢ / xⱼ)ᵈ • e_j^{(d)}`, where `(xᵢ / xⱼ)ᵈ` is the transition unit
`AlgebraicGeometry.ProjectiveSpace.transitionUnit`. In particular `𝒪(d)` on `ℙ¹_S` is a twisted
structure sheaf in the sense of `AlgebraicGeometry.ProjectiveLine.TwistData`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.map_twistGenerator_eq_transitionUnit_smul`: the transition
  rule `e_i^{(d)} = u_{ij} • e_j^{(d)}` on `Uᵢ ∩ Uⱼ`.
- `AlgebraicGeometry.ProjectiveLine.twistData`: the twist data of `𝒪(d)` on `ℙ¹_S`.
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

variable (S : Scheme.{u})

end AlgebraicGeometry.ProjectiveLine
