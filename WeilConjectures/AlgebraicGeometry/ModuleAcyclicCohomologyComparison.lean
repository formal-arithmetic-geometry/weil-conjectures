/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicEffacementLadder
import Mathlib.Algebra.FiveLemma

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- Acyclic module resolutions give comparison for underlying abelian sheaves
(Stacks, Tags 095T and 03FD). -/
theorem Etale.bijective_cohomologyMap_of_module_acyclic
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ) [Fact r.Prime]
    (hzero : ∀ G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))),
      IsIso (globalSectionsUpperStarMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i G))
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj J)) q))
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj M) q) := by
  induction q generalizing M with
  | zero =>
    exact Etale.bijective_cohomologyMap_of_module_acyclic_zero i r hzero M
  | succ q ih =>
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
    let V := (i)^*[AddCommGrpCat.{u + 1}]
    obtain ⟨J, Q, g, δX, δY, hX, hY, hsX, hsY, hδ⟩ :=
      Etale.exists_module_acyclic_effacement_ladder i r hacyclic M q
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      (Sheaf.H.map (U.map g) q) δX (Sheaf.H.map (V.map (U.map g)) q) δY
      (cohomologyMap i (U.obj J) q) (cohomologyMap i (U.obj Q) q)
      (cohomologyMap i (U.obj M) (q + 1))
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map i q (U.map g) x).symm)
      hδ hX hY (ih J).2 (ih Q) hsX hsY

end AlgebraicGeometry
