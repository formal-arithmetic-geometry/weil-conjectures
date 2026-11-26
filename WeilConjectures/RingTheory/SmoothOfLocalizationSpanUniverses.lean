/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.SingularIdeal
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Smooth.Locus
@[expose] public section
universe u v
namespace Algebra
/-- If a set of elements with smooth principal localizations spans the target ideal,
then the target algebra is smooth, allowing different universes. -/
theorem smooth_of_localization_span_universes
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (s : Set A) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Smooth R (Localization.Away (g : A))) :
    Smooth R A := by
  have : FinitePresentation R A :=
    FinitePresentation.of_span_eq_top_target s hs fun g hg ↦ (h ⟨g, hg⟩).2
  refine ⟨?_, inferInstance⟩
  rw [← smoothLocus_eq_univ_iff, ← Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_top,
    ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    basicOpen_subset_smoothLocus_iff]
  exact fun g hg ↦ (h ⟨g, hg⟩).1
end Algebra
