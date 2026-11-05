/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.NativeHomSingle
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist

/-!
# Tate twists as tensor products of Weil complexes

The Tate twist `K ↦ K(m)` of Weil complexes (`AlgebraicGeometry.WeilComplex.tateTwist`) is
defined as the derived tensor product with the lisse Tate sheaf `ℚ̄_ℓ(m)`, through the derived
internal hom out of its dual. This file compares it, followed by a shift `[n]`, with the native
derived tensor product of Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`) with the Weil complex `ℚ̄_ℓ(m)[n]`
(`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`).

## Proof

Put `b = χ_ℓ(σ)ᵐ`, so that `ℚ̄_ℓ(m)` is the constant twist `ℚ̄_ℓ ⊗ 𝓑_b` and the Tate twist is the
derived constant twist `T_b` by `b` (`AlgebraicGeometry.WeilComplex.tateTwistCompιIso`). The
native tensor product `- ⊗ B` with `B = ℚ̄_ℓ(m)[n]` is left adjoint to the native internal hom
`RHom(B, -)`. As `B` is the sheaf `ℚ̄_ℓ ⊗ 𝓑_b` placed in degree `-n`, this internal hom is
`R𝓗om(ℚ̄_ℓ ⊗ 𝓑_b, -)[-n] = T_{b⁻¹}(-)[-n]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilHomSingleIso`), the inverse of the equivalence
`T_b(-)[n]`. Hence `- ⊗ B ≅ T_b(-)[n]`, by uniqueness of left adjoints.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.WeilComplex

open ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.WeilComplex
