module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Global sections of abelian étale sheaves on a zero-dimensional finite-type scheme
 over an algebraically closed field preserve finite colimits.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs;
Stacks Project, Tags 00KH, 00FV, 054M, 03SI and 03QO.
(blueprint: zero-dimensional-global-sections-exact).

Proof: The finite-type dimension-zero theorem makes the underlying space finite and
 discrete. Pass to the reduction, a universal homeomorphism by Tag 054M; its étale
 sheaf category is exactly equivalent to that of C by Tag 03SI, compatibly with
 global sections. The reduction remains finite type over k. Each open-and-closed
 singleton is affine, reduced, and has a unique prime. Its coordinate ring is a
 field: its nilradical is zero and its unique prime is maximal. The residue field
 theorem (Tag 00FV) identifies that field with k. Thus the reduction is the finite
 coproduct of these spectra, including the empty coproduct when C is empty.
 Sheaves on this coproduct are families of sheaves on Spec k. An algebraically
 closed field is strictly henselian. Apply
 `lem-weil-pbc-strictly-henselian-sections-stalk` (Tag 03QO) to R = k and the identity
 geometric point. Its natural germ isomorphism identifies sections on each summand
 with its geometric stalk. Restriction of global sections to the terminal etale
 object is a natural isomorphism. By `prop-weil-pbc-geometric-stalks-exact`, this
 stalk functor preserves finite colimits, hence so do global sections on each
 summand. Consequently global sections are naturally the finite product of these
 exact stalk functors. Finite products of abelian groups are finite biproducts and
 preserve finite colimits. Transport this fact through the exact sheaf equivalence
 for reduction. This proves the displayed finite-colimit preservation; global
 sections already preserve finite limits as a right adjoint. -/
theorem zero_dimensional_global_sections_preservesFiniteColimits
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) :
    PreservesFiniteColimits (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  sorry

end AlgebraicGeometry
