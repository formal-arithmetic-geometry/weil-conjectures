/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Transporting `I • ⊤` along a semilinear map

`Submodule.map_smul''` transports `I • N` along an `R`-linear map. This file records the
variant needed when the two modules live over *different* rings: an additive map `f : M → N`
which is semilinear over a ring map `σ : R →+* S` carries `I • ⊤` into `J • ⊤` as soon as `σ`
carries `I` into `J`.

## Main results

- `Submodule.mem_smul_top_of_semilinear`: the transport of membership in `I • ⊤` along such a
  map.
-/

@[expose] public section

namespace Submodule

variable {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N]

/-- **Membership in `I • ⊤` transports along a semilinear map.** If `f : M →+ N` satisfies
`f (r • m) = σ r • f m` for a ring map `σ : R →+* S` carrying the ideal `I` into the ideal `J`,
then `f` carries `I • ⊤` into `J • ⊤`.

This is the semilinear counterpart of `Submodule.map_smul''`, which is the case of an `R`-linear
map. -/
theorem mem_smul_top_of_semilinear (σ : R →+* S) (f : M →+ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = σ r • f m) (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ r ∈ I, σ r ∈ J) {z : M} (hz : z ∈ I • (⊤ : Submodule R M)) :
    f z ∈ J • (⊤ : Submodule S N) := by
  refine Submodule.smul_induction_on hz (fun r hr n _ ↦ ?_) (fun p q hp hq ↦ ?_)
  · rw [hf]
    exact Submodule.smul_mem_smul (hIJ r hr) trivial
  · rw [map_add]
    exact Submodule.add_mem _ hp hq

end Submodule
