/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordCharts

/-! # Finite images and local upper bounds for resolution words

Source: ILO VIII 2.3.11--2.3.13; the geometric assembly in steps 6--7 of
`lem-trf-normalized-resolution-word-gluing`.
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- A simultaneous coherent chart prescription has finite image and is locally bounded above by its
value at the center point. This is the topological descent step; it neither constructs
the simultaneous prescription nor asserts the summation comparison.

Source: ILO VIII 2.3.11 and 2.3.13, pp. 93--94 (referring to BM/BMT);
agent-written assembly of original node steps 2 and 6--7
(blueprint: lem-trf-resolution-word-finite-local-upper-bounds).

Proof: An admissible stage is reduced and finite type over Q. For maximum extensions,
finite generation of the center ideal on the Noetherian ambient gives finitely generated
Rees charts, hence finite type of the blowup; the strict transform is the schematic
closure of a reduced open and is reduced. The initial and smooth-pullback generators
have the same properties. The coherence hypothesis is supplied on every admissible
prefix and smooth restriction, not just at the current stage. Choose a dimension bound
only to apply the dimension-profile theorem. Summation preserves and reflects head comparisons,
so its finite-image and
closed-upper-level assertions hold for the unsummed head as well. In particular the
regular locus is open. There are finitely many heads. Cover a singular head stratum by
etale presentation neighborhoods. Each engine history has finite word image; a fixed
leading one can be deleted without changing comparisons. Every subset of a Noetherian
space is quasi-compact, so finitely many open etale images suffice on each head stratum.
The finite union of their tail images, over the finitely many heads, together with bottom,
contains the full image. For the local upper bound at a singular point, first exclude the
closed upper level of the least larger occurring head. The current head stratum is then
closed. On this stratum a presentation identifies the tail with the engine tail. Exclude
the closed upper level of its least larger occurring value. This gives a relative open
neighborhood where the tail is at most its value at the point. Etale openness and chart
independence descend that neighborhood to the intrinsic stratum. Extend the relative open
to an ambient open: smaller heads already have smaller words, and regular points have
bottom. At a regular point use the regular open locus. Empty stages require no choices,
and finite disjoint unions use finite unions of these images and neighborhoods.
-/
theorem resolution_word_finite_local_upper_bounds
    (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : ∀ {B : EmbeddedResolutionPair.{u}} {m : ℕ}
      (K : EmbeddedResolutionHistory B m), Admissible ν K →
        (∀ x : K.X, ¬ IsRegularLocalRing (K.X.presheaf.stalk x) →
          Nonempty (ResolutionWordChart R K x)) ∧
        (∀ (x : K.X) (C : ResolutionWordChart R K x), ν K x = C.word) ∧
        (∀ x : K.X, ν K x = ⊥ ↔ IsRegularLocalRing (K.X.presheaf.stalk x)))
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n)
    (hH : Admissible ν H) :
    (Set.range (ν H)).Finite ∧
      ∀ x : H.X, ∃ U : H.X.Opens, x ∈ U ∧ ∀ y ∈ U, ν H y ≤ ν H x := by sorry

end AlgebraicGeometry.EmbeddedResolutionHistory
