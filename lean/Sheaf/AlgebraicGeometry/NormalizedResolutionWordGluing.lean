/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordCharts
import Sheaf.AlgebraicGeometry.ResolutionWordCoherentPrescription
import Sheaf.AlgebraicGeometry.ResolutionWordFiniteLocalUpperBounds

/-! # Gluing dimension-normalized resolution words

Source: ILO VIII 2.3.11--2.3.13, pp. 93--94.
The geometric prescription and its local bounds are assembled with the order comparison
and the closed-upper-level argument here.
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.HilbertSamuel

private theorem sumHead_lt_iff (D : ℕ) (a b : DimensionHead) :
    sumHead D a < sumHead D b ↔ a < b := by
  simp only [sumHead, Prod.Lex.lt_iff, ofLex_toLex]
  rw [(integer_operators (ofLex (ofLex a).2) (ofLex (ofLex b).2) D).2.2.1]
  simp only [toLex_ofLex]

private theorem sumHead_eq_iff (D : ℕ) (a b : DimensionHead) :
    sumHead D a = sumHead D b ↔ a = b := by
  have hmono : StrictMono (sumHead D) := fun a b h ↦ (sumHead_lt_iff D a b).2 h
  exact hmono.injective.eq_iff

private theorem sumResolutionWord_le_iff (D : ℕ) (a b : ResolutionWord) :
    sumResolutionWord D a ≤ sumResolutionWord D b ↔ a ≤ b := by
  cases a with
  | none =>
    cases b with
    | none => exact Iff.rfl
    | some b =>
      change (⊥ : ResolutionWord) ≤ _ ↔ ⊥ ≤ _
      exact ⟨fun _ ↦ bot_le, fun _ ↦ bot_le⟩
  | some a =>
    cases b with
    | none =>
      change (↑(toLex (sumHead D (ofLex a).1, (ofLex a).2)) : ResolutionWord) ≤ ⊥ ↔
        (↑a : ResolutionWord) ≤ ⊥
      simp
    | some b =>
      change (↑(toLex (sumHead D (ofLex a).1, (ofLex a).2)) : ResolutionWord) ≤
        ↑(toLex (sumHead D (ofLex b).1, (ofLex b).2)) ↔
          (↑a : ResolutionWord) ≤ ↑b
      rw [WithBot.coe_le_coe, WithBot.coe_le_coe]
      simp only [Prod.Lex.le_iff, ofLex_toLex, sumHead_lt_iff, sumHead_eq_iff]

private theorem sumResolutionWord_eq_iff (D : ℕ) (a b : ResolutionWord) :
    sumResolutionWord D a = sumResolutionWord D b ↔ a = b := by
  simp only [le_antisymm_iff, sumResolutionWord_le_iff]

end AlgebraicGeometry.HilbertSamuel

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- One simultaneous word assignment, relative to its own least class of finite admissible
histories. The local clause quantifies over every representative, including equivalent
minimal envelopes, overlaps and controlled transforms of a retained head. Existence of a
representative at every singular point makes that clause nonvacuous. At a lower head its
representative starts anew; a vanished old cosupport is never used to present that head.
The word space and assignment are fixed before the auxiliary dimension bound is quantified.

Source: ILO VIII 2.3.11 and 2.3.13, pp. 93--94, node proof steps 1--9
(blueprint: lem-trf-normalized-resolution-word-gluing).

Proof:
1. Telescoping shows that summation and difference on integer sequences are inverse.
The first differing index and its sign are unchanged by summation, including negative entries.
2. Induct on finite admissible prefixes. Finite-type ambient blowups have finite-type charts
by the finitely generated Rees algebra. Schematic strict transforms of reduced schemes are
reduced by lem-trf-reduced-scheme-image. Apply the dimension-profile theorem at each stage.
Its finite-image closed-upper-level modified head has the same comparisons as the raw head.
3. Use the local-presentation theorem in a minimal envelope, with full maximal-order ideal.
Retain all earlier center ideals and exceptional births separately from the empty test
boundary. The minimal-envelope coefficient comparison identifies whole finite-test classes
on common pointed etale charts and preserves the ordered history.
4. Apply the fixed numerical engine and remove its leading one. Its equivalence invariance
in the common support dimension makes the tails agree on all overlaps and choices. Prefix
with the normalized head, and assign the new least element at regular points.
5. Induct on finite prefix length, using the existing controlled transforms and schematic
strict transforms. On a retained head, the presentation tests and engine transforms give the
same tails. After a head drop start a presentation of the new head with its recorded older
boundary; relative birth zero groups these older components while the full ordered earlier
ideals and absolute boundary positions remain recorded. The least admissible class then
restricts the simultaneous prescription. No terminating length is used.
6. At a finite-type stage there are finitely many heads. The Noetherian-space compact-subset
lemma makes each head stratum quasi-compact. Finitely many etale presentation images cover
it, and the engine has finite image on each one. Take the finite union over all heads.
7. Near a singular point first exclude the closed upper level of the least larger head.
On the remaining closed head stratum exclude the least larger tail using engine upper
semicontinuity and finite image. Etale maps are open, so this descends to a neighborhood
where the full word is at most its value at the point. The regular head has an open locus.
8. The complement of any word upper level is open by the preceding local inequality.
The disjoint regular/singular prescription identifies bottom exactly with regularity.
Empty stages and finite disjoint unions use the same alphabet; finite unions of finite
images stay finite and closedness can be checked componentwise.
9. Apply the first-index summation comparison to the second head coordinate. The first
head coordinate, tail and bottom are unchanged, so all comparisons and equality strata
are preserved. The value space and the prescription had no dimension-bound parameter.
-/
theorem normalized_resolution_word_gluing (R : MarkedIdeal.NumericalResolution.{u}) :
    ∃ ν : ValueFamily.{u} HilbertSamuel.ResolutionWord,
      ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n),
        Admissible ν H →
        (∀ x : H.X, ¬ IsRegularLocalRing (H.X.presheaf.stalk x) →
          Nonempty (ResolutionWordChart R H x)) ∧
        (∀ (x : H.X) (C : ResolutionWordChart R H x),
          (R.value C.history ⟨C.supportPoint, C.cosupport⟩).head? =
            some (MarkedIdeal.rational 1) ∧ ν H x = C.word) ∧
        (Set.range (ν H)).Finite ∧
        (∀ v : HilbertSamuel.ResolutionWord, IsClosed {x : H.X | v ≤ ν H x}) ∧
        (∀ x : H.X, ν H x = ⊥ ↔ IsRegularLocalRing (H.X.presheaf.stalk x)) ∧
        ∀ (D : ℕ) (_hD : topologicalKrullDim H.X ≤ (D : WithBot ℕ∞)) (x y : H.X),
          (HilbertSamuel.sumResolutionWord D (ν H x) ≤
              HilbertSamuel.sumResolutionWord D (ν H y) ↔ ν H x ≤ ν H y) ∧
          (HilbertSamuel.sumResolutionWord D (ν H x) =
              HilbertSamuel.sumResolutionWord D (ν H y) ↔ ν H x = ν H y) := by
  obtain ⟨ν, hν⟩ := resolution_word_coherent_prescription R
  refine ⟨ν, ?_⟩
  intro A n H hH
  obtain ⟨hcharts, hwords, hregular⟩ := hν H hH
  obtain ⟨hfinite, hlocal⟩ :=
    resolution_word_finite_local_upper_bounds R ν hν H hH
  refine ⟨hcharts, ?_, hfinite, ?_, hregular, ?_⟩
  · intro x C
    exact ⟨R.normalized C.history C.admissible (C.maximalStages (Fin.last C.length))
      ⟨C.supportPoint, C.cosupport⟩, hwords x C⟩
  · intro v
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨U, hxU, hU⟩ := hlocal x
    refine ⟨U, ?_, U.isOpen, hxU⟩
    intro y hy
    exact fun hv ↦ hx (le_trans hv (hU y hy))
  · intro D _hD x y
    exact ⟨HilbertSamuel.sumResolutionWord_le_iff D (ν H x) (ν H y),
      HilbertSamuel.sumResolutionWord_eq_iff D (ν H x) (ν H y)⟩

end AlgebraicGeometry.EmbeddedResolutionHistory
