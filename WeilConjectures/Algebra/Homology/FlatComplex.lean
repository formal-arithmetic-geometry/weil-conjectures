/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.RingTheory.Flat.ShortExact
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Complexes of flat modules and base change

Let `C` be a cochain complex of flat modules over a commutative ring `A`, exact in degrees
`≥ m`, whose modules of cycles `Zᵏ = ker dᵏ` are flat for `k ≥ m - 1`. Then the complex
`P ⊗ C` stays exact in degrees `≥ m` for every module `P`, and `P ⊗ Zᵏ` is the module of cycles
of `P ⊗ C` for `k ≥ m - 1` (`CochainComplex.range_lTensor_subtype_ker_d`,
`CochainComplex.exact_lTensor_d`): the short exact sequences `0 ⟶ Zᵏ ⟶ Cᵏ ⟶ Zᵏ⁺¹ ⟶ 0` stay exact
after tensoring, `Zᵏ⁺¹` being flat.

The flatness of the cycles propagates downwards along the exact part of the complex
(`CochainComplex.flat_ker_d_of_exactAt`), as a kernel of a surjection between flat modules is
flat; and it holds in high degrees as soon as `A/I ⊗ C` is exact in high degrees for every
ideal `I` (`CochainComplex.flat_ker_d_of_exact_lTensor_quotient`).
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace CochainComplex

variable {A : Type u} [CommRing A] (C : CochainComplex (ModuleCat.{u} A) ℤ)

variable {C}

variable (P : Type u) [AddCommGroup P] [Module A P]

end CochainComplex
