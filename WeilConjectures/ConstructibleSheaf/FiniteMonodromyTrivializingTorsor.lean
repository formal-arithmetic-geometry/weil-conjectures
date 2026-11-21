/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# A connected finite monodromy torsor trivializing a module sheaf

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and the proof of 0A3R.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- A finite locally constant vector-space sheaf is constant on a connected finite
monodromy torsor. Source: Stacks Project, Tag 0DV5 (3), Tag 0DV6, and Tag 0A3R,
proof before the choice of a Sylow subgroup. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P)
      (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (_ : FiniteDimensional (ULift.{u + 1} (ZMod ℓ)) A),
      Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G ≅
        (constantSheaf c.P.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A) := by
  classical
  let R := ULift.{u + 1} (ZMod ℓ)
  obtain ⟨d, hd⟩ := (Scheme.finite_locally_constant_module_values_iff G).1.mpr
    (inferInstance : IsFiniteLocallyConstantSheaf G)
  have hlisse : Scheme.IsLisseModuleSheaf G := ⟨d.cover, hd⟩
  have hsets := (Scheme.lisseModuleSheaf_iff_underlying_finiteLocallyConstant G).mp hlisse
  obtain ⟨Q, hQ, hfin, c, hconn, hconstant⟩ :=
    Scheme.exists_connected_torsor_constant_set_pullback
      ((sheafForget U.smallEtaleTopology).obj G) hsets
  let := hQ
  have := hfin
  have := hconn
  have hmodule := Scheme.module_pullback_isConstant_of_set_pullback R c.π G hconstant
  have := hmodule
  obtain ⟨A, ⟨e⟩⟩ :=
    ((Etale.upperStar (ModuleCat.{u + 1} R) c.π).obj G).mem_essImage_of_isConstant
  have : IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} R) c.π).obj G) :=
    IsFiniteSheaf.upperStar c.π G
  have : IsFiniteSheaf ((constantSheaf c.P.smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj A) := IsFiniteSheaf.of_iso e.symm
  have : Module.Finite R A := Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf (Y := c.P) A
  exact ⟨Q, hQ, hfin, c, hconn, A, inferInstance, ⟨e.symm⟩⟩

end AlgebraicGeometry
