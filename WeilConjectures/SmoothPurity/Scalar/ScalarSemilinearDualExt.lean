/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualEvaluation

/-! # Extensionality for semilinear maps to internal duals

A scalar-extension basis detects maps into a restricted internal dual.

## References

* Stacks Project, Modules on Sites, tensor adjunction (Tags 03EK, 03EL).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- A scalar-extension basis detects maps into a restricted internal dual. -/
theorem scalarSemilinearDualExt
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (M P : proEtaleRingModules T R) (Q : proEtaleRingModules T S)
    (e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α P ≅ Q)
    (c d : M ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj
      ((SheafOfModules.homFunctor (R := S)).obj (Opposite.op Q) |>.obj
        (SheafOfModules.unit _)))
    (h : ∀ (U : T.ProEtᵒᵖ) (φ : M.val.obj U) (x : P.val.obj U),
      ((c.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U
            (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U 1 x)) =
        ((d.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U
            (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U 1 x))) :
    c = d := by
  let H := (SheafOfModules.homFunctor (R := S)).obj (Opposite.op Q) |>.obj
    (SheafOfModules.unit _)
  let F := SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α M H c
  let G := SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α M H d
  let j := ((SheafOfModules.homFunctor (R := S)).mapIso e.op).app
    (SheafOfModules.unit _)
  have hFG : F = G := by
    apply (cancel_mono j.hom).1
    apply SheafOfModules.scalarExtensionDual_hom_ext.{u + 1, u, u + 1} α M P
    intro U s t φ x
    change ((F.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α M U s φ)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U
            (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U t x)) =
      ((G.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α M U s φ)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U
            (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U t x))
    dsimp only [F, G]
    rw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1},
      SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}]
    have ht : e.hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U t x) =
        t • e.hom.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U 1 x) := by
      have hs := SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
        α P U t 1 x
      rw [mul_one] at hs
      rw [← hs, map_smul]
    rw [ht]
    change S.obj.map (𝟙 U.unop).op s •
      (c.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop)))
        (t • e.hom.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U 1 x)) =
      S.obj.map (𝟙 U.unop).op s •
      (d.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop)))
        (t • e.hom.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α P U 1 x))
    rw [map_smul, map_smul, h U φ x]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have hh := congrArg (fun z : _ ⟶ H ↦ z.val.app U
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α M U 1 φ)) hFG
  dsimp only [F, G] at hh
  simpa only [SheafOfModules.scalarExtensionLift_tmul, one_smul] using hh

end WeilConjectures
