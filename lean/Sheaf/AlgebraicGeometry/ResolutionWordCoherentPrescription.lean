/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordCharts

/-! # Coherent local prescriptions on finite embedded histories

Source: ILO VIII 2.3.11--2.3.13; the geometric assembly in steps 2--5 of
`lem-trf-normalized-resolution-word-gluing`.
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- The geometric part of the word prescription: singular points admit actual retained-head
charts, their words agree, and the regular locus receives bottom. No finite-image or
semicontinuity assertion is included.

Source: ILO VIII 2.3.11 and 2.3.13, pp. 93--94 (referring to BM/BMT);
agent-written assembly of original node steps 2--5
(blueprint: lem-trf-resolution-word-coherent-prescription).

Proof: Construct the prescription simultaneously on finite prefixes. At length zero,
use a minimal smooth envelope and a full maximal-order Hilbert--Samuel presentation.
At a singular point normalize its head, and take the numerical engine's word with the
leading entry removed. Minimal-envelope comparison identifies the finite-test classes
on a common pointed etale germ. The support dimensions agree because both envelopes
are minimal. The engine's equivalent-tail and smooth-pullback clauses therefore identify
the resulting words. This proves independence of every choice; prescribe bottom on the
regular locus. For a finite extension, retain the suffix beginning when the current head
was first attained. Pull back every earlier center ideal in its original order. Strict
transform and append the chronological boundary ideals, retaining identity blowups.
The controlled presentation transforms have cosupport equal to the retaining-head locus,
by induction on the finite test sequence. The global maximum restricts on such a locus
to the numerical maximum; patches missing it undergo empty numerical steps. Thus this
suffix is engine-admissible. When the head drops, start a new minimal-envelope presentation;
the older exceptional components have relative birth zero, and their absolute positions
are still recorded. Comparison on common pointed etale germs proves compatibility for
every chart, including transformed ones. Induction on the generators of embedded
admissibility also handles smooth pullbacks and deletion of empty stages. Each assertion
uses only a finite prefix, so no terminating resolution is assumed. At a singular point
the chart word is `some`, hence is not bottom; at a regular point bottom was prescribed.
-/
theorem resolution_word_coherent_prescription (R : MarkedIdeal.NumericalResolution.{u}) :
    ∃ ν : ValueFamily.{u} HilbertSamuel.ResolutionWord,
      ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n),
        Admissible ν H →
        (∀ x : H.X, ¬ IsRegularLocalRing (H.X.presheaf.stalk x) →
          Nonempty (ResolutionWordChart R H x)) ∧
        (∀ (x : H.X) (C : ResolutionWordChart R H x), ν H x = C.word) ∧
        (∀ x : H.X, ν H x = ⊥ ↔ IsRegularLocalRing (H.X.presheaf.stalk x)) := by sorry

end AlgebraicGeometry.EmbeddedResolutionHistory
