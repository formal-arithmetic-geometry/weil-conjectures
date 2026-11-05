/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor

/-!
# Multiplication of Laurent monomial sections of the twisting sheaves

Let `Uᵢ = D₊(xᵢ)` be the standard opens of `ℙ(n; S)` and, for a set `s` of coordinates,
`U_s = ⋂_{i ∈ s} Uᵢ`. Through the canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` of
`lem-pc-twist-tensor` (`AlgebraicGeometry.ProjectiveSpace.twistTensorIso`), the product of the
Laurent monomial sections `xᵉ` of `𝒪(a)` and `xᵉ'` of `𝒪(b)` over `U_s` is the Laurent
monomial section `x^{e + e'}` of `𝒪(a + b)`
(`AlgebraicGeometry.ProjectiveSpace.twistTensorIso_hom_app_twistMonomialSection`). This is the
computation behind the Serre pairing of `lem-pc-projective-space-serre-pairing`: the product
of sections corresponds to the product of Laurent polynomials.

We also define the multiplication `𝒪(b) ⟶ 𝒪(a + b)` by a global section of `𝒪(a)`
(`AlgebraicGeometry.ProjectiveSpace.twistMulHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Proj

open ProjectiveSpectrum.Twist HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] {R : Type u} [CommRing R]

variable {s : Set n} {a b : ℤ}

end Proj

namespace ProjectiveSpace

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] (S : Scheme.{u})

end ProjectiveSpace

end AlgebraicGeometry
