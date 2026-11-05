/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow

/-!

# Tame extensions of a henselian discrete valuation ring and pro-`p` Galois groups

Let `R` be a henselian discrete valuation ring with separably closed residue field `k`,
fraction field `F` and uniformizer `π`. A finite separable extension `L` of `F` of degree `d`
invertible in `k` is totally ramified, so contains a `d`-th root `ρ` of `π`
(`IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`); since `Xᵈ - π` is
irreducible over `F` (Eisenstein), `L = F(ρ)`.

Consequently (`IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem`), if `p` is a prime such
that every natural number vanishing in `k` is divisible by `p`, `Ω` is an algebraic closure of
`F` and `L ⊆ Ω` is an intermediate field containing all roots `ρ` of `π` of order invertible
in `k`, then `Gal(M / L)` is a `p`-group for every finite Galois extension `M / L` in `Ω`: this is
the Sylow argument `IntermediateField.isPGroup_of_forall_mem`.

This generalises the `K⟦X⟧`-specific results of
`WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow`.

## Main statements

- `IsDiscreteValuationRing.irreducible_X_pow_sub_C_algebraMap`: `Xᵈ - π` is irreducible over `F`.
- `IsDiscreteValuationRing.exists_pow_eq_algebraMap_and_mem_adjoin`: a separable element `γ`
  of degree `d` invertible in `k` lies in `F(ρ)` for some `d`-th root `ρ` of `π`.
- `IntermediateField.isPGroup_of_forall_mem_range`: the Sylow argument
  `IntermediateField.isPGroup_of_forall_mem` over a field `L` which is not an intermediate field.
- `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem`: the pro-`p` statement, and its variant
  `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem'` for an arbitrary field `L ⟶ Ω`.
- `IsDiscreteValuationRing.exists_finrank_eq_pow_of_forall_pow_eq_mem`: finite Galois
  subextensions of `E / L` have `p`-power degree.

-/

@[expose] public section

open Polynomial IntermediateField Module IsLocalRing

universe u

namespace IsDiscreteValuationRing

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field F] [Algebra R F]
  [IsFractionRing R F]

end IsDiscreteValuationRing
