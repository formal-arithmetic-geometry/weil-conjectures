/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundTransport
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!
# Reduction of the uniform `Ext` bound to finite subextensions of `ℚ̄_ℓ`

An abstract finite extension `E` of `ℚ_ℓ` embeds into `ℚ̄_ℓ = PadicAlgCl ℓ`; its image is a
finite subextension `E' ⊆ ℚ̄_ℓ`, and the induced isomorphism `E ≃ E'` is a homeomorphism (a
linear isomorphism of finite-dimensional normed spaces over the complete field `ℚ_ℓ`). Hence the
coefficient rings `E̲_X` and `E̲'_X` are isomorphic ring objects, and the uniform `Ext` bound
`ProEtale.HasUniformConstructibleExtBound` transfers from `E'` to `E`
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_finiteIntermediateField`).

Similarly, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`, the rings of integers
`𝒪_E` and `𝒪_{E'}` of `E` and of its image `E'` are isomorphic topological rings, and the bound
transfers from `𝒪_{E'}` to `𝒪_E`
(`ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_finiteIntermediateField`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

variable {T T' : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']

end Profinite

namespace AlgebraicGeometry.ProEtale

/-! ### Abstract finite extensions `E` of `ℚ_ℓ` -/

section ContinuousMap

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

end ContinuousMap

/-! ### Rings of integers of subfields of `ℚ̄_ℓ` -/

section Integers

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

end Integers

end AlgebraicGeometry.ProEtale
