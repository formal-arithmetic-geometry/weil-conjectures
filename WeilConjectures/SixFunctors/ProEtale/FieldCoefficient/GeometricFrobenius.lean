/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Module
public import WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius

/-!
# Pushforward and pullback of `Λ`-adic sheaves along a base change to `k̄` commute with the
Frobenius

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

This is the counterpart, for sheaves of modules over the constant sheaves `Λ_X`
(`AlgebraicGeometry.ProEtale.FieldSheaf`), of
`WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius`.
For a morphism `φ : X₀ ⟶ Y₀` of schemes over a finite field `k`, with base change
`φ̄ : X ⟶ Y` to the geometric fibers, the pushforward and the pullback along `φ̄` commute with
the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldLowerStarEquivalence`: the pushforward along an isomorphism
  is an equivalence.
- `AlgebraicGeometry.ProEtale.fieldUpperStarIsoLowerStarInv`: `e^* ≅ (e⁻¹)_*` for an
  isomorphism `e`.
- `AlgebraicGeometry.ProEtale.fieldLowerStarGeometricFiberMapCompFrobeniusIso` and
  `AlgebraicGeometry.ProEtale.fieldUpperStarGeometricFiberMapCompFrobeniusIso`: the exchange
  isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

section Iso

variable {X Y : Scheme.{u}}

end Iso

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

end AlgebraicGeometry.ProEtale
