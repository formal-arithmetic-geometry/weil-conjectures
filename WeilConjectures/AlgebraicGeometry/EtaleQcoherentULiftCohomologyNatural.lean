/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleQcoherentCohomologyULift
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNaturalSucc

/-! # Naturality of the finite-cover coefficient comparison

## References

* Stacks Project, Tag 03P2
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The coefficient comparison can be chosen to commute with every endomorphism
of the associated abelian sheaf, without assuming that universe lift preserves
injective objects.
(Stacks, Tag 03P2) -/
theorem exists_etaleTensorSectionsSheaf_cohomology_ulift_natural
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    let E := etaleTensorSectionsSheaf F
    let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
    ∃ e : Sheaf.H (L.obj E) q ≃+
        @Sheaf.H _ _ X.smallEtaleTopology E inferInstance (HasExt.standard _) q,
      ∀ (θ : E ⟶ E) (x : Sheaf.H (L.obj E) q),
        e (Sheaf.H.map (L.map θ) q x) =
          @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
            inferInstance (HasExt.standard _)
            _ _ θ q (e x) := by
  dsimp
  cases q with
  | zero =>
      let E := etaleTensorSectionsSheaf F
      let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
      let eL := Sheaf.H.equiv₀ (L.obj E) CategoryTheory.Limits.terminalIsTerminal
      let eS := @Sheaf.H.equiv₀.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology inferInstance
        (HasExt.standard _) E _ CategoryTheory.Limits.terminalIsTerminal
      refine ⟨eL.trans (AddEquiv.ulift.trans eS.symm), ?_⟩
      intro θ x
      change eS.symm (AddEquiv.ulift (eL (Sheaf.H.map (L.map θ) 0 x))) =
        @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
          inferInstance (HasExt.standard _) _ _ θ 0 (eS.symm (AddEquiv.ulift (eL x)))
      rw [@Sheaf.H.equiv₀_symm_naturality.{u + 1, u, u, u + 1} _ _
        X.smallEtaleTopology inferInstance (HasExt.standard _) _
        CategoryTheory.Limits.terminalIsTerminal E E θ]
      apply congrArg eS.symm
      change AddEquiv.ulift (Sheaf.H.equiv₀ (L.obj E)
        CategoryTheory.Limits.terminalIsTerminal (Sheaf.H.map (L.map θ) 0 x)) = _
      rw [← Sheaf.H.equiv₀_naturality]
      rfl
  | succ n =>
      exact exists_etaleTensorSectionsSheaf_cohomology_ulift_natural_succ X F n

end AlgebraicGeometry.Scheme.Modules
