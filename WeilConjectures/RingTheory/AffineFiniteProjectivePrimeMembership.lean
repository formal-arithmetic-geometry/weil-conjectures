/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.FreePrimeMembership
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Module

/-! # Prime membership in a finite projective module is detected at the prime localization

## References

* Stacks Project, Algebra, Lemma 00NX.
-/

@[expose] public section

universe u v
namespace Module

/-- Let `N` be a finite projective `R`-module and `p` a prime ideal of `R`. An element
`s : N` lies in `pN = p • ⊤` if and only if its image `s/1` in `N_p` lies in `pN_p`, where
`N_p = LocalizedModule p.primeCompl N` and `pN_p` is the extension of `p` to
`Localization.AtPrime p` acting on `N_p`. -/
theorem prime_mem_localized_iff
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (s : N) (p : Ideal R) [p.IsPrime] :
    LocalizedModule.mk s 1 ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl N)) ↔
      s ∈ p • (⊤ : Submodule R N) := by
  obtain ⟨n, π, i, _, _, hπ⟩ := Finite.exists_comp_eq_id_of_projective R N
  let iₚ := (IsLocalizedModule.map p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl N)
    (LocalizedModule.mkLinearMap p.primeCompl (Fin n → R)) i).extendScalarsOfIsLocalization
      p.primeCompl (Localization.AtPrime p)
  constructor
  · intro hs
    have hi := Submodule.smul_top_le_comap_smul_top
      (Ideal.map (algebraMap R (Localization.AtPrime p)) p) iₚ hs
    have his : LocalizedModule.mkLinearMap p.primeCompl (Fin n → R) (i s) ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p)
            (LocalizedModule p.primeCompl (Fin n → R))) := by
      simpa [iₚ, LocalizedModule.mkLinearMap_apply,
        IsLocalizedModule.map_LocalizedModules] using hi
    have hfree := (free_prime_mem_localized_iff n (i s) p).1.mp his
    have hmem := Submodule.smul_top_le_comap_smul_top p π hfree
    simpa only [Submodule.mem_comap, ← LinearMap.comp_apply, hπ,
      LinearMap.id_apply] using hmem
  · intro hs
    change LocalizedModule.mkLinearMap p.primeCompl N s ∈ _
    refine Submodule.smul_induction_on hs ?_ ?_
    · intro r hr x _
      rw [map_smul]
      simpa only [algebraMap_smul] using
        (Submodule.smul_mem_smul
          (Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hr)
          (Submodule.mem_top (x := LocalizedModule.mkLinearMap p.primeCompl N x)))
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy

end Module
