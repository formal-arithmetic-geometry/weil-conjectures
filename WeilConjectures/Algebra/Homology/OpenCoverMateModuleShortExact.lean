/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.OpenCoverMateModuleShortExactCore
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The module-level open-cover sequence with its canonical mate maps

## References

* Stacks Project, Cohomology, Tags 08BU and 00A7
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

/-- The canonical mate sequence for a single module sheaf is short exact.
The caller supplies a proof that the displayed composite is zero. -/
theorem open_cover_mate_module_shortExact (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V))
    (F : SheafOfModules.{u} R) :
    let cU := overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    let iU := (aW.homEquiv _ _).symm
      (cU.inv.app F ≫
        (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).map
          (aU.unit.app ((overFunctor.{u} R U).obj F)) ≫
        cU.hom.app (SU.obj ((overFunctor.{u} R U).obj F)))
    let iV := (aW.homEquiv _ _).symm
      (cV.inv.app F ≫
        (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).map
          (aV.unit.app ((overFunctor.{u} R V).obj F)) ≫
        cV.hom.app (SV.obj ((overFunctor.{u} R V).obj F)))
    ∀ hz : biprod.lift iU (-iV) ≫
        biprod.desc (aU.counit.app F) (aV.counit.app F) = 0,
      (ShortComplex.mk (biprod.lift iU (-iV))
        (biprod.desc (aU.counit.app F) (aV.counit.app F)) hz).ShortExact := by
  dsimp
  intro hz
  obtain ⟨hU, hV⟩ := open_cover_mate_module_counit_compatibility X R hR U V hcover
    SU SV SW aU aV aW F
  exact open_cover_mate_module_shortExact_core X R hR U V hcover SU SV SW aU aV aW F
    _ _ hU hV hz

end SheafOfModules
