module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.TraceFormula.BigSmallEtaleRetractionData
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.TraceFormula.BiggerSiteRetraction

/-!
# Exact retraction from big to small étale sheaves

Source: Stacks Project, Etale Cohomology, Tag 0DDI, lemma-cohomological-descent-etale,
with Sites Tags 00XR, 00XT and 00XU (blueprint: lem-trf-big-small-etale-exact-retraction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical big étale retraction has sectionwise restriction on both set and
abelian sheaves, exact abelian direct image, and invertible unit. Source: Stacks
Project, Etale Cohomology, Tag 0DDI and Sites Tags 00XR, 00XT, 00XU
(blueprint: lem-trf-big-small-etale-exact-retraction).

Proof sketch: in compatible larger-universe presentations, the inclusion of the
small étale site into the big étale site is continuous, cocontinuous, fully faithful,
preserves fibre products, and preserves the final object. The bigger-site retraction
theorem then gives the geometric morphism, sectionwise direct image, and invertible
unit. Lifting the adjunction to abelian group objects makes restriction preserve
cokernels, while sectionwise kernels give exactness; the underlying-set unit is the
abelian unit.
-/
theorem bigSmallEtaleExactRetraction (T : Scheme.{u}) :
    Nonempty (BigSmallEtaleRetractionData T) := by
  sorry

end AlgebraicGeometry
