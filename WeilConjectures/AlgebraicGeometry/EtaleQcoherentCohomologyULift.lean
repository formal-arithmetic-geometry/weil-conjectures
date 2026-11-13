/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import WeilConjectures.AlgebraicGeometry.CechComparisonMapNaturality
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Coefficient universe comparison for quasi-coherent étale cohomology

## References

* Stacks Project, Tags 03P2 and 03DW
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Lifting the coefficients of an associated quasi-coherent étale sheaf does not
change its cohomology on a quasi-compact separated scheme (Stacks, Tags 03P2 and 03DW). -/
theorem nonempty_etaleTensorSectionsSheaf_cohomology_ulift
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Nonempty (Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (etaleTensorSectionsSheaf F)) q ≃+
      Sheaf.H (etaleTensorSectionsSheaf F) q) := by
  cases q with
  | zero =>
    exact ⟨(Sheaf.H.equiv₀ _ CategoryTheory.Limits.terminalIsTerminal).trans
      (AddEquiv.ulift.trans
        (Sheaf.H.equiv₀ _ CategoryTheory.Limits.terminalIsTerminal).symm)⟩
  | succ n =>
    classical
    let V := X.affineCover.finiteSubcover
    let U : V.I₀ → X.Opens := fun i ↦ (V.f i).opensRange
    have hU : ∀ i, IsAffineOpen (U i) := fun i ↦ isAffineOpen_opensRange (V.f i)
    have hcover : iSup U = ⊤ := V.iSup_opensRange
    obtain ⟨eL⟩ := nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ X U hU hcover F n
    obtain ⟨c, hc⟩ := ((cechComparisonMapNaturality X U hcover).2 (n + 1)).1 F
    have hI : ∀ (n : ℕ) (y : Fin (n + 1) → V.I₀), IsAffineOpen (⨅ l, U (y l)) := by
      intro n y
      exact IsAffineOpen.iInf (fun l ↦ hU (y l))
    let := moduleCechComparison_isIso_of_affine X U hI hcover F (n + 1) c hc
    let K := (cechComplexFunctor U).obj F.presheafModuleCat
    let T := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}
    let eK := ((K.sc (n + 1)).mapHomologyIso T) ≪≫ T.mapIso (asIso c)
    obtain ⟨_, _, eZ, _, _⟩ := etale_zariski_qcoh_comparison X
    let : HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      HasDerivedCategory.standard _
    let : HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      HasExt.standard _
    let eS :=
      (Abelian.Ext.homAddEquiv.{u + 1, u}.trans
        Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm).trans (eZ F (n + 1)).symm
    exact ⟨eL.trans (eK.addCommGroupIsoToAddEquiv.trans
      (AddEquiv.ulift.trans eS.symm))⟩

end AlgebraicGeometry.Scheme.Modules
