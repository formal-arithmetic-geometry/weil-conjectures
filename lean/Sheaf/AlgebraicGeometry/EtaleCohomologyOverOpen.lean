module

public import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification
public import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility

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

/-- Existence of the canonical open-object cohomology equivalence.
Source: Stacks 03F3 (blueprint: lem-weil-pbc-etale-cohomology-over-open). -/
theorem etaleCohomologyOverOpen {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (Abelian.Ext
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free)) G q ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) q) := by
  exact ⟨etaleCohomologyOverOpenEquiv j G q⟩

end AlgebraicGeometry
