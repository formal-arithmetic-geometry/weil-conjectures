/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.ModuleCupNaiveMap
public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Paper.GlobalTensorPullbackUnderivedData
import Sheaf.Paper.GlobalTensorPullbackDerivedData

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

local instance globalPullbackCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalPullbackMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalPullbackSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalPullbackColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalPullbackPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalPullbackClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance globalPullbackFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

/-- The canonical tensor diagram for a global pullback functor P and a derived
comparison α. Its two paths are the polygon in Stacks Tag 0FP0. This is a
proposition about actual comparison maps, with no postponed data.
Source: Stacks, Tag 0FP0 (blueprint: lem-sc-module-cup-global-tensor-pullback). -/
def moduleCup_globalTensorDiagram
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (L : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (K M : HomotopyCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ)) : Prop :=
  L.map (Functor.LaxMonoidal.μ DerivedCategory.Qh K M) ≫ α.app (K ⊗ M) ≫
      DerivedCategory.Qh.map
        (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
          (ComplexShape.up ℤ) P).app K).app M) =
    (δ (DerivedCategory.Qh.obj K) (DerivedCategory.Qh.obj M)).hom ≫
      (α.app K ⊗ₘ α.app M) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj M)

/-- The canonical bifunctorial tensor isomorphism for
p : (X,O_X) → (pt,Γ(X,O_X)), expressed in Γ(X,O_X)-modules by point evaluation.
The object and map equations specify ordinary p* by inverse image and change of
rings. The ordinary counit/tensor equation fixes its tensor constraint to the
one compatible with the concrete tensor-of-sections map; the derived tensor
isomorphism is normalized on K-flat representatives. All data occur under
existential quantifiers in a theorem, not in a definition choosing an arbitrary
witness.
Source: Stacks, Tag 079U (Lemma 20.27.3), Tags 008A/008Y (ordinary pullback),
and Tag 0B6A (the global ringed-space specialization).
(blueprint: lem-sc-module-cup-global-tensor-pullback)
Proof: take the evaluation equivalence for modules on globalSectionsPoint X.
Compose its inverse with inverse image followed by change of rings along the
adjoint map p⁻¹O_pt → O_X. On morphisms this is inverse image followed by id
 tensor a and sheafification, exactly the two displayed formulas. Ordinary
pullback is strong monoidal: on local tensor generators the constraint sends
(a tensor m) tensor (b tensor n) to ab tensor (m tensor n). Its adjunction
counit is evaluation, so the ordinary tensor/counit equation follows on these
generators, by linearity and sheafification. It is additive and left adjoint.
Derive using K-flat resolutions and the comparison α, invertible on K-flat
complexes. This derivation is absolute: the cofinal K-flat resolution diagram
has invertible comparisons, so postcomposition preserves its universal cone.
For two K-flat representatives their total tensor is K-flat and
pullback is again K-flat. The degreewise strong tensor isomorphism, totalized,
therefore computes an isomorphism L(A tensorᴸ B) → LA tensorᴸ LB. This is
independent of resolutions by naturality and common K-flat refinements.
Naturality descends in both variables from the degreewise tensor isomorphism.
On K-flat representatives the normalization is exactly that totalized map
with the two comparisons α and the lax localization comparison. -/
theorem globalRingedSpace_derivedTensor_pullback_comparison :
    ∃ (e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (_ : Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)))
      (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M)))
      (_ : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
            X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
              ⟨(toGlobalSectionsPoint X).hom.c⟩)
          (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M))
          (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
          eqToHom (h N).symm)
      (hadd : P.Additive) (mon : P.Monoidal)
      (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace),
      letI := hadd
      letI := mon
      letI := adj.isLeftAdjoint
      (∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
        Functor.LaxMonoidal.μ P
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
          P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
        adj.counit.app M ⊗ₘ adj.counit.app N) ∧
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
              moduleCup_globalTensorDiagram X P L α δ
                ((HomotopyCategory.quotient _ _).obj K)
                ((HomotopyCategory.quotient _ _).obj M) := by
  obtain ⟨e, he, P, hP, hm, hadd, mon, adj, hcounit⟩ :=
    exists_globalTensorPullback_underived_data X
  let := hadd
  let := mon
  let := adj.isLeftAdjoint
  obtain ⟨L, α, hL, habs, hflat, δ, hδ, hflatδ⟩ :=
    exists_globalTensorPullback_derived_data X e he P hP hm
  exact ⟨e, he, P, hP, hm, hadd, mon, adj, hcounit,
    L, α, hL, habs, hflat, δ, hδ, hflatδ⟩


end
end AlgebraicGeometry.Scheme.Modules
