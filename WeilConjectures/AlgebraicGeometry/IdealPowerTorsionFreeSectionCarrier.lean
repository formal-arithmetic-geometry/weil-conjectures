/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.CoherentOpenSectionCarrier
import WeilConjectures.AlgebraicGeometry.CoherentIdealPowerTorsionFreeProduct

/-! # An ideal-power-torsion-free carrier of an open section

## References

* Stacks Project, Tag 01YB
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    HSMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (F.val.obj (op V))) (F.val.obj (op V)) where
  hSMul := @SMul.smul Γ(X, V) Γ(F, V) inferInstance

/-- A quasi-coherent section on an ideal complement has a quasi-coherent carrier
inside the original module with zero ideal-power annihilators.
(Stacks, Tag 01YB) -/
theorem exists_idealPower_torsionFree_section_carrier
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (E : X.Modules) [E.IsQuasicoherent] (U : X.Opens)
    (hI : (I.support : Set X) = (U : Set X)ᶜ) (s : E.val.obj (op U)) :
    ∃ (G : X.Modules) (g : G ⟶ E) (t : G.val.obj (op U)),
      G.IsQuasicoherent ∧ Mono g ∧ g.val.app (op U) t = s ∧
      ∀ (n : ℕ) (W : X.Opens) (x : G.val.obj (op W)),
        (∀ (V : X.Opens) (h : V ≤ W)
          (b : (idealSheafPower I.toModulesι n).1.val.obj (op V)),
          ((idealSheafPower I.toModulesι n).2.val.app (op V) b : Γ(X, V)) •
            G.val.map (homOfLE h).op x = 0) → x = 0 := by
  obtain ⟨H, h, t, hqc, hcoh, hm, ht⟩ :=
    exists_coherent_open_section_carrier E U s
  have : H.IsQuasicoherent := hqc
  have : Mono h := hm
  obtain ⟨k, hP, hj, hbij, htf⟩ :=
    exists_coherent_idealPower_torsionFree_product I H hcoh U hI
  let P := idealModuleProduct (idealSheafPower I.toModulesι k).2 H
  let j : P ⟶ H := idealModuleProductι (idealSheafPower I.toModulesι k).2 H
  have : Mono j := hj
  obtain ⟨z, hz⟩ := hbij.2 t
  refine ⟨P, j ≫ h, z, hP, inferInstance, ?_, htf⟩
  change h.val.app (op U) (j.val.app (op U) z) = s
  rw [hz, ht]

end AlgebraicGeometry.Scheme.Modules
