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

/-- Degree zero detects the missing evaluation at the open object: global sections
cannot be additively equivalent to restricted sections if only the latter are trivial. -/
private theorem etaleCohomologyOverOpen_degreeZero_obstruction
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hX : ¬ Subsingleton (G.obj.obj (Opposite.op (⊤_ X.Etale))))
    (hU : Subsingleton
      (((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G).obj.obj
        (Opposite.op (⊤_ U.Etale)))) :
    ¬ Nonempty (Sheaf.H G 0 ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) 0) := by
  rintro ⟨e⟩
  let eX := Sheaf.H.equiv₀ G terminalIsTerminal
  let eU := Sheaf.H.equiv₀
    ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G)
    terminalIsTerminal
  let eSections := eX.symm.trans (e.trans eU)
  apply hX
  exact ⟨fun a b => eSections.injective (hU.elim _ _)⟩

/-- Cohomology over an open étale object agrees with cohomology on the open scheme.

The additive equivalences are natural in the coefficient sheaf; the final conjunct records
compatibility with restriction to smaller open subschemes.  The quasi-coherent clause is the
usual identification of the inverse-image étale sheaf with the étale sheaf attached to the
restricted module.
Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and Sites, Section 00XZ
(blueprint: lem-weil-pbc-etale-cohomology-over-open). -/
-- STATEMENT-DISPUTED: `Sheaf.H G q` is global cohomology on X, not cohomology
-- over the object j : U → X. For q = 0, U empty, X = Spec of an algebraically closed
-- field, and G the constant integer sheaf, the left side is Z and the right side is 0.
-- The DAG instead requires `Sheaf.H' G q` evaluated at the etale object j.
theorem etaleCohomologyOverOpen {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (Sheaf.H G q ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) q) := by
  sorry

end AlgebraicGeometry
