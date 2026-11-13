/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
/-! # Underlying abelian sheaves under open module pullback

Source: Stacks Project, Tag 04J0 and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {X Y : Scheme.{u}}
/-- The coefficient unit is invertible for an open immersion.
Source: Stacks Project, Tag 04J0, localization of ringed sites, and Section 01F7. -/
theorem coefficientUnit_isIso_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) : IsIso (coefficientUnit j M) := by
  have := Topology.IsOpenEmbedding.functor_isContinuous j.isOpenEmbedding
  let a := j.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{u}) (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X)
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} j.base
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let e := b.leftAdjointUniq a
  have hunit : a.unit.app F =
      (SheafOfModules.toSheaf X.ringCatSheaf).map ((restrictAdjunction j).unit.app M) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl
  have hcoeff : coefficientUnit j M = e.hom.app F ≫
      (SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((restrictFunctorIsoPullback j).hom.app M) := by
    apply (b.homEquiv _ _).injective
    simp only [coefficientUnit, coeff, b, Equiv.apply_symm_apply]
    erw [b.homEquiv_naturality_right]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, hunit]
    change (SheafOfModules.toSheaf X.ringCatSheaf).map (pullbackUnit j M) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map ((restrictAdjunction j).unit.app M) ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map
          ((pushforward j).map ((restrictFunctorIsoPullback j).hom.app M))
    rw [← Functor.map_comp]
    congr 1
    exact pullbackUnit_eq_of_isOpenImmersion j M
  rw [hcoeff]
  infer_instance
end AlgebraicGeometry.Scheme.Modules
