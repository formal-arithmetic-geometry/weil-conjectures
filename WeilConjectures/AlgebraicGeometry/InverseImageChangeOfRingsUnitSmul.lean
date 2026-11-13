/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Scalar compatibility of the inverse-image extension unit

## References

* Stacks Project, Tags 008X and 03EK.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Prove the tensor identity over plain modules before applying it to the sheaf sections.
private theorem map_one_tmul_smul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) {N : ModuleCat.{u} S}
    (sh : (ModuleCat.extendScalars f).obj M ⟶ N) (r : R) (m : M) :
    f r • sh ((1 : S) ⊗ₜ[R, f] m) = sh ((1 : S) ⊗ₜ[R, f] (r • m)) := by
  rw [← sh.hom.map_smul]
  congr 1
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  let : Module R S := Module.compHom _ f
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  change _ = (f r * 1) ⊗ₜ[R] m
  rw [mul_one]

/-- The additive inverse-image unit, followed by extension and sheafification, is
semilinear for the ring inverse-image unit followed by the extension ring map.
(Stacks, Tags 008X, 03EK, 01SB) -/
theorem inverseImage_changeOfRings_unit_smul
    {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Y.Sheaf CommRingCat.{u})
    (B : X.Sheaf CommRingCat.{u}) (t : TopCat.Sheaf.inverseImageRing f A ⟶ B)
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
    (V : (TopologicalSpace.Opens Y)ᵒᵖ) (c : A.obj.obj V) (n : G.val.obj V) :
    let W := (Opens.map f).op.obj V
    let eta := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app
          ((SheafOfModules.toSheaf _).obj G)).hom.app V
    let etaR := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) CommRingCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app A).hom.app V
    let sh := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj B).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t
            (TopCat.Sheaf.inverseImageModule f A G))).app W
    (t.hom.app W).hom (etaR c) •
      sh ((1 : B.obj.obj W) ⊗ₜ[(TopCat.Sheaf.inverseImageRing f A).obj.obj W,
        (t.hom.app W).hom] eta n) =
      sh ((1 : B.obj.obj W) ⊗ₜ[(TopCat.Sheaf.inverseImageRing f A).obj.obj W,
        (t.hom.app W).hom] eta (c • n)) := by
  intro W eta etaR sh
  rw [(Classical.choose_spec (TopCat.Sheaf.exists_inverseImageModuleInstances f A G)).2 V c n]
  exact map_one_tmul_smul (t.hom.app W).hom
    ((TopCat.Sheaf.inverseImageModule f A G).val.obj W) sh (etaR c) (eta n)

end AlgebraicGeometry.Scheme.Modules
