/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.DualLocalEvaluation
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Finite-free exterior frames on a trivializing open
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry
open Scheme.Modules (wedge)

set_option backward.isDefEq.respectTransparency false in
/-- Finite-free exterior sheaves admit wedge bases, and internal dual evaluation identifies
sections of the dual exterior sheaf with the linear dual of its sections.
(Stacks, Tag 0BRT) -/
theorem exterior_dual_local_frames (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op V)) (M.val.obj (op V)))
      (φ : Fin r → (Scheme.Modules.dual M).val.obj (op V))
      (b : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n).val.obj (op V)))
      (d : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorPower M n).val.obj (op V)))
      (c : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op V) ≃ₗ[
        X.presheaf.obj (op V)] Module.Dual (X.presheaf.obj (op V))
          ((Scheme.Modules.exteriorPower M n).val.obj (op V))),
      (∀ (j : Fin r) (x : M.val.obj (op V)),
        (φ j).app (op (Over.mk (𝟙 V))) x = a.coord j x) ∧
      (∀ s, b s = wedge (M := (Scheme.Modules.dual M)) (r := n) (U := V)
        (φ ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ s, d s = wedge (M := M) (r := n) (U := V)
        (a ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ (ψ : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op V))
        (x : (Scheme.Modules.exteriorPower M n).val.obj (op V)),
        c ψ x = ψ.app (op (Over.mk (𝟙 V))) x) := by
  classical
  let : CommRing (X.ringCatSheaf.obj.obj (op V)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op V)))
  let c₀ : M.val.obj (op V) ≃ₗ[X.presheaf.obj (op V)]
      (ULift.{u} (Fin r) → X.presheaf.obj (op V)) :=
    SheafOfModules.sectionsLinearEquivOfIsoFree e (op (Over.mk g))
  let a : Module.Basis (Fin r) (X.presheaf.obj (op V)) (M.val.obj (op V)) :=
    Module.Basis.ofEquivFun
      (c₀.trans (LinearEquiv.funCongrLeft _ _ Equiv.ulift.symm))
  obtain ⟨cM, hcM⟩ := Scheme.Modules.dual_local_evaluation_equiv X M U
    (ULift.{u} (Fin r)) e V g
  let φBasis := a.dualBasis.map cM.symm
  let φ : Fin r → (Scheme.Modules.dual M).val.obj (op V) := φBasis
  have hφ (j : Fin r) (x : M.val.obj (op V)) :
      (φ j).app (op (Over.mk (𝟙 V))) x = a.coord j x := by
    rw [← hcM]
    simp [φ, φBasis]
  let eDual : (Scheme.Modules.dual M).over U ≅
      SheafOfModules.free (ULift.{u} (Fin r)) :=
    SheafOfModules.overHomObjIso M (SheafOfModules.unit X.ringCatSheaf) U ≪≫
      ((SheafOfModules.homFunctor (X.sheaf.over U)).flip.obj
        (SheafOfModules.unit (X.ringCatSheaf.over U))).mapIso e.symm.op ≪≫
      SheafOfModules.homObjFreeUnitIso.{u} (R := X.sheaf.over U) _
  obtain ⟨⟨eExt⟩, hExt⟩ := Scheme.Modules.exteriorSheaf_local_free_comparison X M n U r e
  obtain ⟨_, hExtDual⟩ := Scheme.Modules.exteriorSheaf_local_free_comparison X
    (Scheme.Modules.dual M) n U r eDual
  let q := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).app (op V)).hom
  let qDual := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    ((_root_.PresheafOfModules.exteriorPower (R := _) (Scheme.Modules.dual M).val n))).app
      (op V)).hom
  let d := (a.exteriorPower n).map (LinearEquiv.ofBijective q (hExt V g))
  let b := (φBasis.exteriorPower n).map (LinearEquiv.ofBijective qDual (hExtDual V g))
  obtain ⟨c, hc⟩ := Scheme.Modules.dual_local_evaluation_equiv X
    (Scheme.Modules.exteriorPower M n) U (ULift.{u} (Set.powersetCard (Fin r) n))
    eExt V g
  refine ⟨a, φ, b, d, c, hφ, ?_, ?_, hc⟩
  · intro s
    change qDual ((φBasis.exteriorPower n) s) = _
    rw [exteriorPower.basis_apply]
    rfl
  · intro s
    change q ((a.exteriorPower n) s) = _
    rw [exteriorPower.basis_apply]
    rfl

end AlgebraicGeometry
