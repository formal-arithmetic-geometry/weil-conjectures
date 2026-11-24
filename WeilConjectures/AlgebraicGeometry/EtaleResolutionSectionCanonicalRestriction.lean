/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalWholeToOpen
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpen

/-!
# Restriction of normalized resolution comparisons

## References

* Stacks Project, Tags 0A50 and 03F3
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Canonical comparisons commute with whole-to-open and open-to-open restriction.
(Stacks, Tag 03F3) -/
theorem resolutionSection_canonical_restriction {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    (∀ W q x, c.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (c.globalEquiv q x)) ∧
    (∀ (A B : X.Opens) (h : A ≤ B) q x,
      c.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (c.openEquiv B q x)) := by
  constructor
  · exact resolutionSection_canonical_whole_to_open G I c
  · exact resolutionSection_canonical_open_to_open G I c

end AlgebraicGeometry.Etale
