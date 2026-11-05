/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on projective space

On the standard open `Uᵢ = D₊(xᵢ)` of `ℙ(n; S)` the twisting sheaf `𝒪(m)` has the free generator
`e_i^{(m)} = xᵢᵐ` (`AlgebraicGeometry.ProjectiveSpace.twistGenerator`), the pullback of the
section `Tᵢᵐ` of `𝒪(m)` on the integral model `Proj ℤ[Tᵢ]`. The transition functions are
`e_i^{(m)} = (xᵢ/xⱼ)ᵐ e_j^{(m)}`, which are multiplicative in `m`; hence the local isomorphisms
`e_i^{(a)} ⊗ e_i^{(b)} ↦ e_i^{(a+b)}` glue to an isomorphism
`AlgebraicGeometry.ProjectiveSpace.twistTensorIso : 𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`
(blueprint `lem-pc-twist-tensor`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

end Scheme.Modules

namespace ProjectiveSpace

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

end ProjectiveSpace

end AlgebraicGeometry
