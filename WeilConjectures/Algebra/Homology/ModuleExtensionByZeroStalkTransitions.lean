/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkTransitionCoherence

/-!
# Stalk transitions for extension by zero

Transition maps between extensions by zero along inclusions of opens, and their stalks.

## References

* Stacks Project, Sheaves, Tags 00A7 (2)-(4) and 00A5
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- For a global module sheaf `F`, the counit at the top open is an isomorphism, the extensions by
zero of the restrictions of `F` admit transition maps along inclusions of opens, and for `x` in
`W` the stalk of `F` at `x` is isomorphic to the stalk of the `W` extension compatibly with them. -/
theorem moduleExtensionByZero_stalk_transitions (X : RingedSpace.{u}) :
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
  intro F
  refine ⟨?_, ?_⟩
  · let ff : (SheafOfModules.overFunctor.{u} (moduleRings X) ⊤).FullyFaithful :=
      { preimage := fun g ↦
          { val :=
              { app := fun U ↦ g.val.app (op (Over.mk (homOfLE (le_top : U.unop ≤ ⊤))))
                naturality := by
                  intro U V f
                  exact g.val.naturality
                    (Over.homMk (U := Over.mk (homOfLE (le_top : V.unop ≤ ⊤)))
                      (V := Over.mk (homOfLE (le_top : U.unop ≤ ⊤)))
                      f.unop (by subsingleton)).op } }
        map_preimage := by
          intro M N g
          ext U x
          rfl
        preimage_map := by
          intro M N g
          ext U x
          rfl }
    let := ff.full
    let := ff.faithful
    infer_instance
  · let iota := fun (W W' : Opens X) (h : W ≤ W') ↦
        ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _).symm
          ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
            (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
              ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
                ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)))
    refine ⟨iota, ?_, ModuleExtensionByZeroStalkTransitionCoherence X F⟩
    intro W W' h
    exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry
