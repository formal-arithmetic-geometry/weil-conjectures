/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkComponents
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkNaturality
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks

/-! # Scalar compatibility of restriction on module stalks

## References

* Stacks Project, Sheaves, Section 6.31, Lemma 6.31.1 (3), Definition 6.31.2 (4) (Tags 009Z, 00A1)
-/

@[expose] public section
open CategoryTheory TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry

/-- Restriction alone induces a natural linear stalk comparison, with its germ formula. -/
theorem exists_moduleRestrictionStalk_morphism (X : RingedSpace.{u}) (W : Opens X)
    (x : X) (hx : x ∈ W) :
    ∃ c : SheafOfModules.overFunctor.{u} (moduleRings X) W ⋙
        (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
        RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩ ⋙
        ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom ⟶
      RingedSpace.moduleStalkFunctor X x,
      ∀ (F : SheafOfModules.{u} (moduleRings X)) (V : Opens W)
        (hV : (⟨x, hx⟩ : W) ∈ V)
        (s : F.val.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj V))),
        (c.app F) (TopCat.Presheaf.germ (C := Ab.{u})
          (X := (X.restrict W.isOpenEmbedding).carrier)
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F)).val.presheaf
          V ⟨x, hx⟩ hV s) =
        TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
          (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩ s := by
  classical
  obtain ⟨c, hc⟩ := exists_moduleRestrictionStalk_components X W x hx
  let S := SheafOfModules.overFunctor.{u} (moduleRings X) W ⋙
    (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
    RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩ ⋙
    ModuleCat.restrictScalars
      (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom
  let T := RingedSpace.moduleStalkFunctor X x
  let n : S ⟶ T :=
    { app := c
      naturality := by
        intro F G f
        exact moduleRestrictionStalk_components_natural X W x hx c hc f }
  exact ⟨n, hc⟩

end AlgebraicGeometry
