/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkInside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkTransitions
public import Mathlib.Topology.Sheaves.Module

/-! # Stalks and maps for extension by zero of modules

## References

* Stacks Project, Sheaves, Tag 00A7, clauses (2)--(4), and Tag 00A5
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry

/-- The extension-by-zero stalk formula and the canonical maps for nested opens: stalks outside
the open vanish, stalks inside the open are identified with those of the original sheaf, and the
transition maps are compatible with the counits. -/
theorem module_extensionByZero_stalk_maps (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (G : SheafOfModules.{u} ((moduleRings X).over W)) (x : X),
      x ∉ W → IsZero ((RingedSpace.moduleStalkFunctor X x).obj
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj G))) ∧
    (∀ (W : Opens X) (x : X) (hx : x ∈ W),
      ∃ e : (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
          RingedSpace.moduleStalkFunctor (X.restrict (Opens.isOpenEmbedding W)) ⟨x, hx⟩ ⋙
          ModuleCat.restrictScalars
            (X.toPresheafedSpace.restrictStalkIso (Opens.isOpenEmbedding W) ⟨x, hx⟩).inv.hom ≅
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ⋙
          RingedSpace.moduleStalkFunctor X x,
        ∀ (G : SheafOfModules.{u} ((moduleRings X).over W)) (V : Opens W)
          (hV : (⟨x, hx⟩ : W) ∈ V)
          (s : ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.obj (op V)),
          (e.hom.app G) (TopCat.Presheaf.germ (C := Ab.{u})
              (X := (X.restrict (Opens.isOpenEmbedding W)).carrier)
              ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.presheaf
              V ⟨x, hx⟩ hV s) =
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  G).val.presheaf
              ((Opens.isOpenEmbedding W).isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩
              (((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app
                G).val.app
                (op (Over.mk (homOfLE (Set.image_subset_iff.2 (fun y _ => y.2))))) s)) ∧
    (∀ F : SheafOfModules.{u} (moduleRings X),
      IsIso ((Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F) ∧
      ∃ iota : (∀ (W W' : Opens X), W ≤ W' →
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F) ⟶
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))),
        (∀ (W W' : Opens X) (h : W ≤ W'),
          (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _
              (iota W W' h) =
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
              (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
                ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
              (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))) ∧
        (∀ W : Opens X, iota W W le_rfl = 𝟙 _) ∧
        (∀ (W W' W'' : Opens X) (h : W ≤ W') (h' : W' ≤ W''),
          iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')) ∧
        (∀ W : Opens X,
          iota W ⊤ le_top ≫
              (Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F =
            (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app F) ∧
        ∃ e : (∀ (W : Opens X) (x : X), x ∈ W →
            ((RingedSpace.moduleStalkFunctor X x).obj F ≅
              (RingedSpace.moduleStalkFunctor X x).obj
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F)))),
          (∀ (W : Opens X) (x : X) (hx : x ∈ W),
            (e W x hx).inv =
              (RingedSpace.moduleStalkFunctor X x).map
                ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app
                  F)) ∧
          (∀ (W W' : Opens X) (h : W ≤ W') (x : X) (hx : x ∈ W),
            (e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h) =
              (e W' x (h hx)).hom)) := by
  exact ⟨moduleExtensionByZero_stalk_outside X,
    ⟨moduleExtensionByZero_stalk_inside X, moduleExtensionByZero_stalk_transitions X⟩⟩

end AlgebraicGeometry
