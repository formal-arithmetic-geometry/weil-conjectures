/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.RingTheory.CompletionRegularKernelPreservation
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.TraceFormula.CompleteLocalCIPresentationIndependence
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Regular-sequence kernels and completed quotients

Source: Stacks Project, dpa.tex, Tags 09Q1 and 09PZ
(blueprint: lem-trf-regular-quotient-completion-kernel-test).
-/

@[expose] public section

universe u v

open RingTheory

/-- For a quotient of a regular local ring, regular-sequence generation of the
ideal is equivalent to regular-sequence generation of the kernel of any
surjective presentation of its maximal-ideal-adic completion by a regular
local ring.

Source: Stacks Project, dpa.tex, Tags 09Q1 (equivalence (1) and (2)) and 09PZ
(independence of the regular-local surjection onto a complete local ring)
(blueprint: lem-trf-regular-quotient-completion-kernel-test).

Proof: Apply the canonical completion comparison to identify regular-sequence
 generation of `I` with that of the kernel of the canonical map from the
 completion of `R`.  The independence-of-presentation lemma then identifies
 that kernel with the kernel of the given surjection `π`.  The hypotheses that
 the quotient completion is complete local and that both source rings are
 regular local are supplied by the completion and quotient lemmas listed in
 the DAG proof dependencies.  Empty lists are allowed by the regular-sequence
 definition.
-/
theorem regularQuotientCompletionKernelTest
    {R : Type u} {Q : Type v} [CommRing R] [CommRing Q]
    [IsRegularLocalRing R] [IsRegularLocalRing Q]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (π : Q →+* AdicCompletion
      (Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R)) (R ⧸ I))
    (hπ : Function.Surjective π) :
    (∃ xs : List R,
      RingTheory.Sequence.IsRegular R xs ∧
        Ideal.ofList xs = I ∧
          ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ↔
      (∃ ys : List Q,
        RingTheory.Sequence.IsRegular Q ys ∧
          Ideal.ofList ys = RingHom.ker π ∧
            ∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal Q) := by
  classical
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI)
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let n := Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R)
  have hn : n = IsLocalRing.maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalRing (AdicCompletion n (R ⧸ I)) := by
    rw [hn]
    infer_instance
  have : IsNoetherianRing (AdicCompletion n (R ⧸ I)) :=
    AdicCompletion.isNoetherianRing n
  have hcomplete (J : Ideal (R ⧸ I)) (hJ : J = IsLocalRing.maximalIdeal (R ⧸ I))
      [IsLocalRing (AdicCompletion J (R ⧸ I))] :
      IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion J (R ⧸ I)))
        (AdicCompletion J (R ⧸ I)) := by
    subst J
    infer_instance
  have := hcomplete n hn
  have : IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    (AdicCompletion.isRegularLocalRing_iff R).mp inferInstance
  let q₀ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+*
      AdicCompletion n (R ⧸ I) :=
    (AdicCompletion.exists_local_completion_quotient R (R ⧸ I)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).2.choose
  have hc := completionRegularKernelPreservation I hI (IsNoetherian.noetherian I)
  change Function.Surjective q₀ ∧ _ at hc
  have : IsLocalHom q₀ := IsLocalHom.of_surjective q₀ hc.1
  have : IsLocalHom π := IsLocalHom.of_surjective π hπ
  exact hc.2.trans (completeLocalCIPresentationIndependence
    (AdicCompletion n (R ⧸ I)) (AdicCompletion (IsLocalRing.maximalIdeal R) R) Q
    q₀ π hc.1 hπ)

end
