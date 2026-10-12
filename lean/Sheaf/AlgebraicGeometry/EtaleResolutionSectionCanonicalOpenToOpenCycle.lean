module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison
import Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafUnitCoherence
import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Cocycle-level restriction identity underlying the canonical open comparison.
Source: Stacks Project, Tags 0A50 and 03F3; normalized Hom-cocycle calculation.
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-open-to-open-cycle)

The proof expands the two `open_cocycle` normalization identities, rewrites the
Ext class of the restricted cocycle using `InjectiveResolution.mk₀_comp_extMk`,
and applies the identity-generator coherence and exact inverse-image composition
comparison. This is the cocycle calculation before passing to arbitrary homology
classes via surjectivity of `homologyπ`.
-/
theorem resolutionSection_canonical_open_to_open_cycle {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (c : ResolutionSectionCanonicalComparison G I)
    (A B : X.Opens) (h : A ≤ B) (q : ℕ)
    (z : (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).cycles q) :
    let K := (((etaleSectionFunctor (Scheme.Etale.mk A.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex)
    let L := (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex)
    let φ := etaleSectionMap
      (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
        Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex
    c.openEquiv A q (K.homologyπ q ((HomologicalComplex.cyclesMap φ q) z)) =
      openCohomologyRestriction h G q (c.openEquiv B q (L.homologyπ q z)) := by
  sorry

end AlgebraicGeometry.Etale
