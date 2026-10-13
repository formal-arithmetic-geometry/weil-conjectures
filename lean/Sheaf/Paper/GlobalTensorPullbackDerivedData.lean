/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute

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

local instance globalDerivedDataCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalDerivedDataMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalDerivedDataSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalDerivedDataColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalDerivedDataPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalDerivedDataClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance globalDerivedDataFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

/-- Absolute derived tensor pullback after point evaluation.
Source: Stacks Tags 079U, 06YJ, 06XN and 0FP0.
(blueprint: lem-sc-global-tensor-pullback-derived-data)
Proof: compose the point evaluation inverse with concrete tensor pullback. Evaluation
is an exact equivalence, so its termwise functor preserves K-flat complexes and their
quasi-isomorphisms. Transport the absolute left derivation of concrete tensor pullback
across this equivalence. Its comparison is invertible on K-flat representatives. For
K-flat K and M their total tensor is K-flat, and concrete pullback preserves K-flatness.
Totalizing the inverse strong tensor constraint computes the displayed tensor
isomorphism. Its naturality on K-flat complexes descends through localization in both
variables; common K-flat refinements identify different choices. The resulting
isomorphism has the displayed normalization because on K-flat representatives its
construction is the totalized inverse tensor constraint composed with the comparison
isomorphisms. Transport of the absolute Kan extension through an exact equivalence
preserves its universal property after every indicated postcomposition. These arguments
apply to the zero complex and to all integer degrees without a boundedness assumption. -/
theorem exists_globalTensorPullback_derived_data
    (e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (he : Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)))
      (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M)))
      (hm : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
            X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
              ⟨(toGlobalSectionsPoint X).hom.c⟩)
          (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M))
          (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
          eqToHom (h N).symm)
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint] :
    ∃ (L : DerivedCategory
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
        (α : DerivedCategory.Qh ⋙ L ⟶
          P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        L.IsLeftDerivedFunctor α
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
        (∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ⥤
            DerivedCategory
              (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))),
          (L ⋙ H).IsLeftDerivedFunctor
            ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α H)
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) ∧
        (∀ K : CochainComplex
            (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ,
          (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
            IsIso (α.app ((HomotopyCategory.quotient _ _).obj K))) ∧
        ∃ δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B,
          (∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
            L.map (f ⊗ₘ g) ≫ (δ A' B').hom =
              (δ A B).hom ≫ (L.map f ⊗ₘ L.map g)) ∧
          ∀ K M : CochainComplex
              (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ,
            (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
            (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat M →
              (let K' := (HomotopyCategory.quotient _ _).obj K
               let M' := (HomotopyCategory.quotient _ _).obj M
               L.map (Functor.LaxMonoidal.μ DerivedCategory.Qh K' M') ≫
                   α.app (K' ⊗ M') ≫ DerivedCategory.Qh.map
                     (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
                       (ComplexShape.up ℤ) P).app K').app M') =
                 (δ (DerivedCategory.Qh.obj K') (DerivedCategory.Qh.obj M')).hom ≫
                   (α.app K' ⊗ₘ α.app M') ≫
                     Functor.LaxMonoidal.μ DerivedCategory.Qh
                       ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj K')
                       ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj M')) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
