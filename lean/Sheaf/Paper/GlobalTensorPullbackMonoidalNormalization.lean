/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module
public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.Paper.ModuleCupNaiveMap
public import Sheaf.Algebra.Homology.KFlatPullback
/-! # Tensor-counit normalization of the global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
/-- Concrete global pullback admits the tensor constraint normalized by its counit.
Source: Stacks Tags 008A, 008Y and 0FKU.
(blueprint: lem-sc-global-tensor-pullback-monoidal-normalization)
Proof: the inverse image and change-of-rings formula identifies P with p* after point
evaluation. Inverse image preserves the sheaf tensor product, and extension of scalars
has the tensor constraint multiplying the two O_X coefficients. These constraints are
isomorphisms; their associativity and unit identities follow on local pure tensors.
Transport this strong monoidal structure to P using the prescribed object and map
identifications. The canonical evaluation adjunction has the asserted counit identity
on pure tensors: both sides send (a tensor m) tensor (b tensor n) to ab times m tensor n.
Linearity and the sheafification universal property give the identity on sheaves.
For the given adjunction, use the unique isomorphism of left adjoints to the same
right adjoint to transport the constraint and its unit. Its compatibility with the
counits transports the displayed identity as well. Zero modules and the empty scheme
satisfy the same generator identities. -/
theorem globalTensorPullback_monoidal_normalization
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
    [P.Additive]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace) :
    ∃ mon : P.Monoidal,
      letI := mon
      ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
        Functor.LaxMonoidal.μ P
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
          P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
        adj.counit.app M ⊗ₘ adj.counit.app N := by sorry
end
end AlgebraicGeometry.Scheme.Modules
