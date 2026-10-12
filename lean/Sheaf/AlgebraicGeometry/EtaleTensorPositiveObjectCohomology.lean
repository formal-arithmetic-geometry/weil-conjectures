module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural
import Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Positive object cohomology of the associated etale tensor-sections sheaf vanishes
on affine opens.
Source: Stacks Project, Etale Cohomology, Tag 03P2 (affine case), and Cohomology
on Sites, Tag 03F3. https://stacks.math.columbia.edu/tag/03P2
(blueprint: lem-sc-etale-tensor-positive-object-cohomology)

Proof: Fix an affine open U and put j = U.ι. Localization at the etale object j
identifies object cohomology with global cohomology on the small etale site of U.
Restriction of an injective resolution computes this comparison: restriction
along an open immersion preserves injectives because extension by zero is an exact
left adjoint. At v : V -> U, normalized tensor-pullback composition identifies
Gamma(V,(v composed with j)^*F) with Gamma(V,v^*(j^*F)); the unit-normalized
composition law makes these identifications commute with restriction maps.
Thus the restricted sheaf is the tensor-sections sheaf of F restricted to U,
which is quasi-coherent. Affine etale quasi-coherent acyclicity gives zero in
degree n+1. To use the large-coefficient localization comparison, lift the
injective resolution and its evaluation complexes; the coefficient-lift
resolution comparison commutes with evaluation and homology. The lift reflects
zero groups, giving vanishing in the original coefficient universe. The empty
open is affine and the same argument applies. No assertion is made on non-affine
opens: an affine cover gives local vanishing, not global cohomology vanishing. -/
theorem etaleTensorPositiveObjectCohomology
    (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    ∀ U : X.Opens, IsAffineOpen U → IsZero
      (Sheaf.H' (etaleTensorSectionsSheaf F) (n + 1)
        (Scheme.Etale.mk U.ι)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
