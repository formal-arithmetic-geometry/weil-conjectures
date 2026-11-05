/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.Mathlib.RingTheory.Etale.Kaehler

/-!
# Étale coordinates adapted to a complete intersection

Let `A` be a smooth `R`-algebra whose Kähler differentials have constant rank `n`, and let
`I = (f₁, …, f_c)` be an ideal of `A` such that `B = A ⧸ I` is smooth over `R` with Kähler
differentials of constant rank `m`, where `m + c = n`. Then near every prime `p ⊇ I` of `A`
there are `g₁, …, g_m : A` such that `R[t₁, …, t_c, s₁, …, s_m] → A[1/a]`, `t ↦ f`, `s ↦ g`,
is étale for some `a ∉ p`.

The proof follows the conormal sequence `I/I² → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → 0`: choosing the
`g` so that the `d gbⱼ` form a basis of `Ω[B⁄R]` at `p`, the differentials `d fᵢ, d gⱼ` span
`Ω[A⁄R]` at `p`, hence form a basis there (both sides being free of rank `n`), hence after
inverting some `a ∉ p`. One concludes by the étaleness criterion
`MvPolynomial.etale_aeval_of_basis_kaehlerDifferential`.

## Main results

- `KaehlerDifferential.ker_map_le_of_surjective`: for a surjection `A → B` with kernel `I`, the
  kernel of `Ω[A⁄R] → Ω[B⁄R]` is contained in `A • d(I) + I • Ω[A⁄R]`.
- `Algebra.exists_etale_aeval_sumElim_of_ker`: the étale coordinates described above.
-/

@[expose] public section

open KaehlerDifferential TensorProduct

namespace KaehlerDifferential

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

end KaehlerDifferential

namespace IsLocalizedModule

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  [IsLocalization S Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] (f : M →ₗ[R] M')
  [IsLocalizedModule S f]

end IsLocalizedModule

namespace Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

end Algebra
