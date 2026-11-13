/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Global ringed-space pullback comparisons

The ringed-space map throughout is `toGlobalSectionsPoint X`, with target
`globalSectionsPoint X`, not a morphism of schemes. Modules on this point are
identified with Γ(X,O_X)-modules by evaluation. No condition on X is imposed.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance globalCounitCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing (X.presheaf.obj (op ⊤)))
/-- The global ringed-space counit comparison square, for the ordinary pullback `P` and its
left-derived comparison `α`, with the derived adjunction induced from the ordinary adjunction
(Stacks, Tag 0FP1). -/
theorem globalRingedSpace_derivedCounit_comparison
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive]
    (L : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Functor.IsLeftDerivedFunctor
      (L ⋙ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Functor.IsRightDerivedFunctor
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙ L)
        (Functor.whiskerRight
            (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit L ≫
          (Functor.associator _ _ _).hom)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    L.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        (((adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) α
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit).counit.app
            (DerivedCategory.Qh.obj K)) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K) := by
  exact (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) α
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit K

end
end AlgebraicGeometry.Scheme.Modules
