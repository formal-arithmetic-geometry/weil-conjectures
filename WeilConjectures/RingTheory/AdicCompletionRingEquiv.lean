/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.RingTheory.PairHenselizationCompletionData

/-!
# Adic completion and ring equivalences

We show that a ring isomorphism `R ≃+* S` carrying `I` to `J` induces an isomorphism of adic
completions, compatible with the canonical maps.

## References

* Stacks Project, More on Algebra, Definition 07GH and Proposition 07PV.
-/

@[expose] public section

universe u v

/-- A ring isomorphism `e : R ≃+* S` with `J = I.map e` induces a ring isomorphism of the
`I`-adic completion of `R` with the `J`-adic completion of `S`, compatible with the canonical
maps from `R` and `S`. -/
theorem AdicCompletion.exists_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S) (h : J = I.map e) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      E.toRingHom.comp (algebraMap R (AdicCompletion I R)) =
        (algebraMap S (AdicCompletion J S)).comp e.toRingHom := by
  subst J
  obtain ⟨E, _, hE⟩ := RingTheory.pair_henselization_completion_data R S I e.toRingHom
    (by
      intro n hn
      let q := Ideal.quotientEquiv (I ^ n) ((I ^ n).map e.toRingHom) e rfl
      exact q.bijective)
  refine ⟨E, ?_⟩
  apply RingHom.ext
  intro r
  apply E.symm.injective
  change E.symm (E (algebraMap R (AdicCompletion I R) r)) =
    E.symm (algebraMap S (AdicCompletion (I.map e.toRingHom) S) (e r))
  rw [RingEquiv.symm_apply_apply]
  exact (DFunLike.congr_fun hE r).symm
