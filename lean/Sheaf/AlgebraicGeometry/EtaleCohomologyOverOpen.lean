module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence

/-! # Étale cohomology over an open object

Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and Sites, Section 00XZ
(blueprint: lem-weil-pbc-etale-cohomology-over-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Cohomology over an open étale object agrees with cohomology on the open scheme.

The additive equivalences are natural in the coefficient sheaf; the final conjunct records
compatibility with restriction to smaller open subschemes.  The quasi-coherent clause is the
usual identification of the inverse-image étale sheaf with the étale sheaf attached to the
restricted module.
Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and Sites, Section 00XZ
(blueprint: lem-weil-pbc-etale-cohomology-over-open). -/
theorem etaleCohomologyOverOpen {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (Sheaf.H G q ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) q) := by
  sorry

end AlgebraicGeometry
