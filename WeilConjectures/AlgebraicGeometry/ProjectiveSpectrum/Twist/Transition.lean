/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj

/-!
# Transition functions of the powers `fᵐ` of the twisting sheaves

For homogeneous elements `f` and `g` of degree `1` of a graded ring `𝒜`, the sections `fᵐ` and
`gᵐ` of `𝒪(m)` over `D₊(f)` and `D₊(g)` are related by `fᵐ = (f / g)ᵐ • gᵐ` on
`D₊(f) ∩ D₊(g)`.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist Scheme.Modules

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {f g : A}

end AlgebraicGeometry.Proj
