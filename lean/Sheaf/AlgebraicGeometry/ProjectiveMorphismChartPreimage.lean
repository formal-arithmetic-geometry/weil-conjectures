/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Chart preimages and coordinate ratios for generating sections

Source: Stacks Project, Constructions, Lemmas 01NE and 01N8 via 01NA
(blueprint: lem-weil-pbc-projective-morphism-chart-preimage).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

/-- The morphism defined by generating sections of an invertible module pulls each
standard chart back to the nonvanishing locus of its coordinate section. On that open,
the pullback of the coordinate ratio is the unique scalar multiplying the denominator
section to give the numerator section.

Source: Stacks Project, Constructions, Lemmas 01NE and 01N8 via 01NA
(blueprint: lem-weil-pbc-projective-morphism-chart-preimage).

Proof:
1. Compose the defining pairing with the second projection to reduce both claims to the
   integral morphism (def-weil-pbc-morphism-to-projective-space-by-sections).
2. The functor-of-points isomorphism identifies the pulled-back twisting module and its
   coordinate sections with L and s_i (lem-weil-pbc-projective-space-functor-of-points).
   On the integral chart, T_j trivializes O(1), its nonvanishing locus is D_+(T_j), and
   T_l = (T_l/T_j) T_j (lem-weil-pbc-projective-space-twisting-sheaf-charts).
3. Pullback of a section has fibre value v tensor 1; scalar extension between residue
   fields preserves nonzero vectors (lem-weil-pbc-invertible-pullback-tensor). Transport
   along the isomorphism in step 2 to identify the chart preimage with Y_{s_j}.
4. Apply the O-linear tensor-pullback adjunction unit to the chart relation in step 2,
   then apply the isomorphism to L (def-pc-module-pullback). This gives the required
   scalar equation. Multiplication by s_j is bijective on its nonvanishing open
   (lem-weil-pbc-nonvanishing-section-trivializes), proving uniqueness of the scalar.
-/
theorem homOfGeneratingSections_chart_preimage (n : ℕ) {Y S : Scheme.{u}}
    (g : Y ⟶ S) (L : Y.Modules) [L.IsInvertible]
    (s : ULift.{u} (Fin (n + 1)) → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    ∀ j : ULift.{u} (Fin (n + 1)),
      (homOfGeneratingSections _ g L s hs ⁻¹ᵁ standardOpen _ S j : Set Y) =
        nonvanishingLocus L ((s j).val (op ⊤)) ∧
      ∀ (l : ULift.{u} (Fin (n + 1))),
        (L.presheaf.map (homOfLE
            (le_top : homOfGeneratingSections _ g L s hs ⁻¹ᵁ standardOpen _ S j ≤ ⊤)).op
          ((s l).val (op ⊤)) =
            (homOfGeneratingSections _ g L s hs).app (standardOpen _ S j)
              (coordRatio _ S j l) •
              L.presheaf.map (homOfLE
                (le_top : homOfGeneratingSections _ g L s hs ⁻¹ᵁ standardOpen _ S j ≤ ⊤)).op
                ((s j).val (op ⊤))) ∧
        ∀ (a : Γ(Y, homOfGeneratingSections _ g L s hs ⁻¹ᵁ standardOpen _ S j)),
          L.presheaf.map (homOfLE
              (le_top : homOfGeneratingSections _ g L s hs ⁻¹ᵁ standardOpen _ S j ≤ ⊤)).op
            ((s l).val (op ⊤)) =
              a • L.presheaf.map (homOfLE
                (le_top : homOfGeneratingSections _ g L s hs ⁻¹ᵁ standardOpen _ S j ≤ ⊤)).op
                ((s j).val (op ⊤)) →
            a = (homOfGeneratingSections _ g L s hs).app (standardOpen _ S j)
              (coordRatio _ S j l) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
