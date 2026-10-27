module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCohomologyEdge
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import WeilConjectures.AlgebraicGeometry.Cohomology.Leray
import Sheaf.CategoryTheory.FirstQuadrantRowCollapse

/-! # Cohomology along affine morphisms of algebraic spaces

Source: Stacks Project, Spaces Cohomology, Tag 0D2U, lemma-relative-affine-cohomology
(blueprint: lem-sfb-space-affine-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical edge is invertible for affine maps and quasi-coherent coefficients.
Source: Stacks Project, Spaces Cohomology, Tag 0D2U
(blueprint: lem-sfb-space-affine-cohomology).

Proof:
1. Apply lem-sfb-space-affine-higher-direct-image-vanishing (Tag 073H) to the underlying
   additive sheaf of F: all positive higher direct images vanish. Affineness and
   quasi-coherence are the only geometric and coefficient hypotheses.
2. Apply the abelian-sheaf Leray specialization of det-thm-groth-ss (Tags 0732 and 0733).
   The module and additive direct images have the same chart sections, identified by
   representableModuleDirectImageComparison. Its bottom edge is precisely inverse-image
   pullback followed by the adjunction counit, the map representableCohomologyEdge.
3. All positive rows vanish. The canonical bottom edge is an isomorphism by
   lem-weil-pbc-first-quadrant-row-collapse. In degree zero it is the defining identity
   of global sections; this argument uses global sections of the topos, without treating
   a general algebraic space as a scheme object of its small etale site. -/
theorem affine_cohomology_edge_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (hf : MapIsAffine f) (F : Y.Modules) (hF : F.IsQuasicoherent) (q : ℕ) :
    IsIso (AddCommGrpCat.ofHom
      (representableCohomologyEdge f (affine_relativelyRepresentable f hf) F q)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
