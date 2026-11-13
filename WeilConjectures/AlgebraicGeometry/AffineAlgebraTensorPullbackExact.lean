/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.AffineAlgebraStalkFlat
import WeilConjectures.AlgebraicGeometry.StalkFlatTensorPullbackKernels
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Exact tensor pullback to an affine morphism's direct-image algebra

## References

* Stacks Project, Tag 0AVW
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The underived tensor pullback to the direct-image algebra of an affine
morphism is exact, with its action specified on objects and morphisms (Stacks, Tag 0AVW). -/
theorem affine_algebra_tensorModulePullback_exact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap
        (toDirectImageAlgebraSpace f).hom.base X.toRingedSpace.sheaf
        (directImageAlgebraSpace f).sheaf ⟨(toDirectImageAlgebraSpace f).hom.c⟩)
      (TopCat.Sheaf.inverseImageModule (toDirectImageAlgebraSpace f).hom.base
        (directImageAlgebraSpace f).sheaf M))
    (hm : ∀ {M N} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap
          (toDirectImageAlgebraSpace f).hom.base X.toRingedSpace.sheaf
          (directImageAlgebraSpace f).sheaf ⟨(toDirectImageAlgebraSpace f).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toDirectImageAlgebraSpace f).hom.base
          (directImageAlgebraSpace f).sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap (toDirectImageAlgebraSpace f).hom.base
          (directImageAlgebraSpace f).sheaf M a) ≫ eqToHom (h N).symm) :
    PreservesFiniteLimits P ∧ PreservesFiniteColimits P := by
  obtain ⟨Q, hQ, hmQ, hadd, ⟨adj⟩⟩ :=
    RingedSpace.exists_tensorModulePullback (toDirectImageAlgebraSpace f)
  let e : P ≅ Q := NatIso.ofComponents
    (fun M ↦ eqToIso ((h M).trans (hQ M).symm)) (by
      intro M N a
      dsimp only [eqToIso]
      rw [hm, hmQ]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans])
  let : Q.Additive := hadd
  let : Q.IsLeftAdjoint := adj.isLeftAdjoint
  let : P.Additive := Functor.additive_of_iso e.symm
  let : PreservesFiniteColimits P := preservesFiniteColimits_of_natIso e.symm
  have {M N : SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))}
      (a : M ⟶ N) : PreservesLimit (parallelPair a 0) P :=
    RingedSpace.stalkFlat_tensorModulePullback_preservesKernels
      (toDirectImageAlgebraSpace f)
      (fun x ↦ affine_algebra_stalkMap_flat f x) P h hm a
  exact ⟨Functor.preservesFiniteLimits_of_preservesKernels P, inferInstance⟩

end AlgebraicGeometry
