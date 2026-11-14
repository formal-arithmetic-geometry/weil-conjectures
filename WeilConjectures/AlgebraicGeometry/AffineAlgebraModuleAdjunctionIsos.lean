/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionFiniteLimits
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionUnitIso
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionCounitIso

/-! # The underived affine algebra adjunction

## References

* Stacks Project, Tag 0AVW
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Tensor pullback for the direct-image algebra is exact, and its adjunction
maps are isomorphisms on quasi-coherent modules (Stacks, Tags 0AVW and 01SB). -/
theorem affine_algebra_module_adjunction_isos
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) :
    Limits.PreservesFiniteLimits P ∧
    (∀ M : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)),
      M.IsQuasicoherent → IsIso (a.unit.app M)) ∧
    (∀ K : SheafOfModules.{v} (moduleRings X.toRingedSpace),
      K.IsQuasicoherent → IsIso (a.counit.app K)) := by
  let G := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let : G.IsRightAdjoint := a.isRightAdjoint
  let b := Adjunction.ofIsRightAdjoint G
  let : Limits.PreservesFiniteLimits G.leftAdjoint :=
    affine_algebra_module_adjunction_preserves_finite_limits f
  refine ⟨Limits.preservesFiniteLimits_of_natIso (b.leftAdjointUniq a), ?_, ?_⟩
  · intro M hM
    have hunit : IsIso (b.unit.app M) := affine_algebra_module_adjunction_unit_iso f M hM
    let := hunit
    rw [← b.unit_leftAdjointUniq_hom_app a M]
    infer_instance
  · intro K hK
    have hcounit : IsIso (b.counit.app K) := affine_algebra_module_adjunction_counit_iso f K hK
    let := hcounit
    rw [← a.leftAdjointUniq_hom_app_counit b K]
    infer_instance

end AlgebraicGeometry
