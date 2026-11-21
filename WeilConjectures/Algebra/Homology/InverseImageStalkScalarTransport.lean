/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransportBeta
import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransportNaturality

/-!
# Scalar transport for inverse-image stalks on ringed spaces

## References

* Stacks Project, Sheaves, Tags 008H and 0098
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped ChangeOfRings

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport tensor scalars through the inverse-image ring and module stalk comparisons. -/
theorem exists_ringed_inverseImage_stalk_scalar_transport
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
    (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf) (x : X) :
    let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
    let ψ : TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
        (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x →+* X.presheaf.stalk x :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom
    let ρ := ψ.comp k.hom
    ∃ (c : ∀ M : RingedSpace.Modules Y,
        (RingedSpace.moduleStalkFunctor Y (f x)).obj M ≃+
          TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
            (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x)
      (β : ∀ M : RingedSpace.Modules Y,
        (ModuleCat.extendScalars ρ).obj
            ((RingedSpace.moduleStalkFunctor Y (f x)).obj M) ≅
          (ModuleCat.extendScalars ψ).obj
            (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u})
              (X := X.carrier) (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x)
              (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
                (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x))),
      (∀ (M : RingedSpace.Modules Y) (b : X.presheaf.stalk x)
        (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
        (β M).hom (b ⊗ₜ[_, ρ] m) = b ⊗ₜ[_, ψ] (c M m)) ∧
      (∀ (M N : RingedSpace.Modules Y) (a : M ⟶ N)
        (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
        c N ((RingedSpace.moduleStalkFunctor Y (f x)).map a m) =
          PresheafOfModules.stalkAddMap
            (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a).val (c M m)) := by
  dsimp
  obtain ⟨c, hs, hn⟩ := exists_inverseImage_stalk_comparison_natural X Y f x
  have : IsIso (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x) :=
    (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} f Y.presheaf x).isIso_hom
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u}
    ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf)
  let k : Y.presheaf.stalk (f x) ⟶
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
        (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x :=
    TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
  have hk := ConcreteCategory.bijective_of_isIso k
  let ψ := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom
  have hβ := fun M ↦ exists_inverseImage_stalk_scalar_transport_beta k.hom hk ψ
    ((RingedSpace.moduleStalkFunctor Y (f x)).obj M)
    (ModuleCat.of _ (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
      (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x)) (c M) (hs M)
  choose β hβ using hβ
  exact ⟨c, β, hβ, hn⟩

end
