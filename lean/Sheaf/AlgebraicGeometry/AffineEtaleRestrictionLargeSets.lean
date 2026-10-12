module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Topologies 04HR and Sites 03A0.
Proof: every etale scheme has an affine open cover. The full affine inclusion is
fully faithful, so equality and lifting of arrows hold on identity covers.
Finite affine etale coverings are coverings in the full site, and every covering
of an affine etale scheme has a finite affine refinement. These facts identify
fullAffineEtaleTopology with the topology induced from smallEtaleTopology and
make the inclusion a dense subsite. Extend an affine sheaf by compatible families
on affine covers of each etale object; the sheaf condition makes the extension
independent of the cover and gives its restriction back. Conversely the sheaf
condition identifies any full-site sheaf with this extension of its restriction.
These constructions are inverse on morphisms as well as objects. Families and
compatibility conditions lie in Type (u + 1), so this construction works in that
coefficient universe without shrinking the section sets.
(blueprint: lem-stage3-affine-etale-restriction-large-sets) -/
theorem fullAffineEtale_large_sets_equivalence (S : Scheme.{u}) :
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type (u + 1))
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by sorry

end AlgebraicGeometry.Scheme
