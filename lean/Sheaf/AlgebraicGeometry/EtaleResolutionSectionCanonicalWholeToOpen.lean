/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison
import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Whole-to-open restriction of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3 (2), expanded on Hom cocycles.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Whole-to-open restriction identity for a normalized comparison.
Source: Stacks Project, Tag 03F3 (2), and Tag 0A50, proof;
the Hom-cocycle expansion of the parent restriction argument.
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-whole-to-open)

Proof: Let K be the resolution evaluated at the terminal etale object. Since
K.homologyπ q is an epimorphism of abelian groups, write the given class as the
image of a cycle z. The constant-sheaf adjunction identifies K.iCycles q z
with a unique morphism f from the constant lifted integers to I.cocomplex.X q.
Naturality in the coefficient sheaf identifies its composite with the differential
with the differential of the section, which is zero; thus f is a Hom cocycle.
Let a be the free-sheaf map from the free sheaf on W to the constant integer
sheaf corresponding to the constant section 1 on W. The free-sheaf sections
adjunction identifies a composed with f with the restriction of the original
section. Naturality of homologyπ identifies its cycle class with the homology
map of etaleSectionMap. Apply c.global_cocycle and c.open_cocycle to the two
cycles. The formula I.mk₀_comp_extMk identifies the second Ext class with
precomposition of the first by a. In etaleOpenObjectCohomologyMap, pulling
back a and precomposing with etaleOpenFreeSheafUnit W is the inverse of the
constant-sheaf comparison: both maps classify the section 1 by the constant
sheaf adjunction. Functoriality of Ext under the exact inverse-image functor
and associativity of Ext composition now give cohomologyMap W.ι on the first
class. Surjectivity of homologyπ gives the equality for every class. The
argument uses no positive-degree or nonempty-open assumption, so includes
q = 0, the empty open, identity restriction and the zero sheaf. -/
theorem resolutionSection_canonical_whole_to_open {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    ∀ W q x, c.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (c.globalEquiv q x) := by sorry
end AlgebraicGeometry.Etale
