/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Additivity of the trace along short exact sequences

For a short exact sequence `0 → M → N → P → 0` of modules over a commutative ring with `M` and
`P` finite free, and endomorphisms `φM`, `φN`, `φP` compatible with the maps,
`tr φN = tr φM + tr φP` (`LinearMap.trace_eq_trace_add_trace_of_exact`). This is the linear
algebra behind blueprint `prop-trf-trace-formal-laws`, items (2) and (4).
-/

@[expose] public section

namespace LinearMap

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

/-- The trace of an endomorphism of a subsingleton module is zero. -/
lemma trace_eq_zero_of_subsingleton [Subsingleton M] (φ : M →ₗ[R] M) : trace R M φ = 0 := by
  rw [Subsingleton.elim φ 0, map_zero]

/-- **Additivity of the trace on short exact sequences**: for a short exact sequence
`0 → M → N → P → 0` of modules with `M`, `P` finite free (hence also `N`) and endomorphisms
`φM`, `φN`, `φP` commuting with the maps, `tr φN = tr φM + tr φP`. The sequence splits since `P`
is projective, and with a splitting `id = f ∘ r + s ∘ g` the claim follows from the cyclicity of
the trace. -/
theorem trace_eq_trace_add_trace_of_exact [Module.Free R M] [Module.Finite R M] [Module.Free R P]
    [Module.Finite R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) {φM : M →ₗ[R] M} {φN : N →ₗ[R] N}
    {φP : P →ₗ[R] P} (hM : φN ∘ₗ f = f ∘ₗ φM) (hP : g ∘ₗ φN = φP ∘ₗ g) :
    trace R N φN = trace R M φM + trace R P φP := by
  have := Module.Free.of_exact hfg hf hg
  have := Module.Finite.of_exact hfg hg
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, hef, heg⟩ := hfg.splitSurjectiveEquiv hf ⟨l, hl⟩
  set r := fst R M P ∘ₗ e.toLinearMap
  set s := e.symm.toLinearMap ∘ₗ inr R M P
  have hrf : r ∘ₗ f = LinearMap.id := by
    rw [hef]
    ext
    simp [r]
  have hgs : g ∘ₗ s = LinearMap.id := by
    rw [heg]
    ext
    simp [s]
  have hid : f ∘ₗ r + s ∘ₗ g = LinearMap.id := by
    rw [hef, heg]
    ext x
    simp only [add_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_inl, coe_fst,
      coe_inr, coe_snd, id_coe, id_eq, r, s]
    rw [← map_add, Prod.fst_add_snd, LinearEquiv.symm_apply_apply]
  calc trace R N φN = trace R N ((φN ∘ₗ f) ∘ₗ r) + trace R N ((φN ∘ₗ s) ∘ₗ g) := by
        rw [← map_add, comp_assoc, comp_assoc, ← comp_add, hid, comp_id]
    _ = trace R M (r ∘ₗ φN ∘ₗ f) + trace R P (g ∘ₗ φN ∘ₗ s) := by
        rw [trace_comp_comm' (φN ∘ₗ f) r, trace_comp_comm' (φN ∘ₗ s) g]
    _ = trace R M φM + trace R P φP := by
        rw [hM, ← comp_assoc, ← comp_assoc, hP, hrf, comp_assoc, hgs, id_comp,
          comp_id]

end LinearMap
