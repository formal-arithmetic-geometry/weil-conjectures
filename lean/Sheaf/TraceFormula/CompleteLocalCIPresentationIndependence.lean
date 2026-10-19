/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.CohenStructurePowerSeriesSurjection
import Sheaf.RingTheory.CompletionRegularKernelPreservation
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import Sheaf.RingTheory.PowerSeriesFieldCohenFsAdic
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.TraceFormula.RegularLocalSurjectionKernelComparison

/-!
# Independence of a regular-sequence kernel from the regular-local presentation

Source: literature/stacks-project/dpa.tex, Tag 09PZ (lemma-ci-well-defined)
(blueprint: lem-trf-complete-local-ci-presentation-independence).

## Main statement

Stage-2 delivery attribution: Q83, 2026-10-18.

* `completeLocalCIPresentationIndependence` states that the regular-sequence
  kernel condition is independent of a regular-local presentation of a complete
  Noetherian local ring.
-/

@[expose] public section

universe u v w

open RingTheory

/-- Source: Stacks Project, dpa.tex, Tag 09PZ, lemma-ci-well-defined
(blueprint: lem-trf-complete-local-ci-presentation-independence).

The proof first passes to completions, then compares both completed presentations
with a fixed Cohen power-series presentation by continuous lifting and adic
power-series evaluation.  The resulting composable surjections are compared by
the regular-local-surjection kernel comparison.  Empty sequences are allowed.
-/
theorem completeLocalCIPresentationIndependence
    (A : Type u) (P : Type v) (Q : Type w) [CommRing A] [CommRing P] [CommRing Q]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsRegularLocalRing P] [IsRegularLocalRing Q]
    (q₀ : P →+* A) (q : Q →+* A)
    [IsLocalHom q₀] [IsLocalHom q]
    (hq₀ : Function.Surjective q₀) (hq : Function.Surjective q) :
    ((∃ xs : List P,
        RingTheory.Sequence.IsRegular P xs ∧
          Ideal.ofList xs = RingHom.ker q₀ ∧
          ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal P) ↔
      (∃ ys : List Q,
        RingTheory.Sequence.IsRegular Q ys ∧
          Ideal.ofList ys = RingHom.ker q ∧
          ∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal Q)) := by
  sorry

end
