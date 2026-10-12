module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement
import Sheaf.AlgebraicGeometry.StandardFpqcQuotientTopology

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- An fpqc covering detects openness of a subset of its base.

Source: Stacks Project, Descent, Lemma Tag 03N0, proof after the set construction;
https://stacks.math.columbia.edu/tag/03N0.
(blueprint: lem-weil-pbc-fpqc-detects-openness)

Proof: Openness is local on the base, so restrict to each affine open of S and
base-change the covering to it. Fpqc coverings are stable under base change, and
the inverse images of the restricted subset remain open by continuity. Identify
this affine base with Spec R. Apply exists_fpqc_affine_standard_refinement to
obtain finitely many affine opens V_j of covering members. The induced map from
R to the product of their coordinate rings is faithfully flat. Its factors give
R-algebra structures on those rings. Each inverse image of the subset under the
spectrum of a factor map is open: the corresponding affine scheme is isomorphic
to V_j, and its map to the base factors through a covering member with open
inverse image. Apply standard_fpqc_quotient_topology to this finite family.
Thus the subset is open on every affine open of S, and hence on S. This argument
allows an empty refinement when the affine base is empty; then its subset is
empty and open. -/
theorem isOpen_of_fpqc_preimages
    {S : Scheme.{u}} {I : Type v} {T : I → Scheme.{u}}
    (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (V : Set S) (hV : ∀ i, IsOpen (g i ⁻¹' V)) : IsOpen V := by
  sorry

end AlgebraicGeometry
