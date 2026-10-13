/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.ModuleCupGlobalTensorPullback

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

local instance globalTensorCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalTensorMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalTensorSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalTensorColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalTensorPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalTensorClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance globalTensorFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

/-- The full global tensor comparison polygon, for all integer complexes,
not just flat or bounded ones. P, L, α and δ are the pullback data and the
canonical tensor isomorphism of the global tensor theorem. Normalization on
K-flat pairs fixes δ to that canonical isomorphism; naturality alone would not
suffice. The conclusion is precisely the two composites of Stacks Tag 0FP0,
with the two left downward arrows composed as α_K tensor α_M and with the
bottom arrow the lax localization comparison. The right downward arrows are
α at the total tensor, followed by the inverse ordinary tensor constraint.
Source: Stacks, Tag 0FP0, Lemma 20.27.5.
(blueprint: lem-sc-module-cup-global-tensor-comparison)
Proof: choose K-flat resolutions K0 → K and M0 → M. Their total tensor is
K-flat. The ordinary tensor-pullback comparison is natural, so the rectangle
from p*Tot(K0 tensor M0) to p*Tot(K tensor M), followed by the ordinary
inverse tensor constraint, commutes with the tensor of the two resolution
maps. Naturality of α and the lax comparison of Qh identifies the top/right
path with the left path computed on K0,M0 followed by the bottom tensor maps.
By normalization δ on K0,M0 gives that left path. Naturality of δ identifies
its transport with δ on K,M. Localized resolution maps are isomorphisms and
remain so under L and tensor; cancel their tensor composite to obtain the
polygon for K,M. Every homotopy-category object has a complex representative,
so this proves the equation as stated. This uses no assertion that p is flat,
no preservation of arbitrary quasi-isomorphisms by p*, and no condition on X. -/
theorem globalRingedSpace_tensor_comparison_diagram
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (L : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (hnat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      L.map (f ⊗ₘ g) ≫ (δ A' B').hom = (δ A B).hom ≫ (L.map f ⊗ₘ L.map g))
    (hflat : ∀ K M : CochainComplex
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ,
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat M →
        moduleCup_globalTensorDiagram X P L α δ
          ((HomotopyCategory.quotient _ _).obj K)
          ((HomotopyCategory.quotient _ _).obj M))
    (K M : HomotopyCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ)) :
    moduleCup_globalTensorDiagram X P L α δ K M := by sorry

end
end AlgebraicGeometry.Scheme.Modules
