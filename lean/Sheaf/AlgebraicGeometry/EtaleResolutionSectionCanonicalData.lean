/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison
import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMapBijective

/-!
# Existence of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Existence of comparisons normalized by the Hom-to-sections adjunction.
Source: Stacks Project, Tag 0A50 (sections of resolutions), Tag 03F3 (localization).
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-data)

Proof: For the constant integer sheaf on X, the constant-sheaf adjunction and
 evaluation at 1 identify Hom into each term of I with global sections. These
 additive equivalences commute with differentials. Thus the Hom-complex computation
 of Ext identifies its cocycle classes with homology of the global section complex.
 Use the inverse of `I.extAddEquivCohomologyClass` to obtain the global equivalence;
 its defining value on a cocycle is exactly `I.extMk`. For every open W, replace
 the constant sheaf by the free abelian sheaf on the representable W. The
 sheafification/free/Yoneda adjunction gives `sectionsEquiv` in each degree,
 naturally in the resolution term, and hence again an equivalence of cocycle
 classes. Compose the resulting homology-to-Ext equivalence with the independently
 constructed `etaleOpenObjectCohomologyMap`, which is bijective by localization:
 inverse image along W preserves injectives, since exact extension by zero is
 its left adjoint. The composite has the stated open cocycle value. This
 constructs all opens from the same adjunction, with no compatibility claimed
 here. In degree zero use the kernel of the first differential; in positive
 degrees quotient cycles by boundaries. Empty opens and zero sheaves give zero
 groups and the same construction. -/
theorem exists_resolutionSection_canonical_comparison {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G) :
    Nonempty (ResolutionSectionCanonicalComparison G I) := by sorry

end AlgebraicGeometry.Etale
