/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthThreeLocalCohomologyVanishing
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedHOneLocalCohomologyComparison

/-! # First cohomology of the structure sheaf on a depth-three puncture

Source: Stacks Project, Tags 0BK0 and 0AVY.
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- The first structure-sheaf cohomology of a depth-three puncture vanishes.

Source: Stacks Project, Tag 0BK0 (Lemma 51.8.2) and Tag 0AVY (Lemma 47.11.1).
(blueprint: lem-sbc-depth-three-puncture-h-one)

Proof: Apply the affine local-cohomology comparison to Spec R with support
in its closed point, whose defining ideal is the maximal ideal. Since an
associated quasi-coherent sheaf on Spec R has no positive cohomology, the
comparison gives H^1(W,O_W) = H^2_m(R). The depth hypothesis and 0AVY make
the latter zero. The unit module has underlying additive sheaf O_W, so its
Modules.H is exactly the cohomology in this comparison. Vanishing means
that every element equals zero, which gives Subsingleton. No completeness
or regularity hypothesis is used. The assertion includes the empty open:
its sheaf cohomology is zero. -/
theorem depth_three_puncture_h_one
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1) := by
  apply punctured_h_one_subsingleton_of_local_cohomology_vanishing R W hW
  exact depth_three_local_cohomology_vanishing R hdepth

end AlgebraicGeometry.Scheme
