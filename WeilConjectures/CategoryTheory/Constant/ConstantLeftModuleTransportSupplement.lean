/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import WeilConjectures.CategoryTheory.ConstantLeftModuleTransport

/-!
# Exact inverse image for constant left-module sheaves

Source: Stacks Project, Sites, Proposition 00YV (2), (5), (6), its fixed-ring
scalar-endomorphism proof, and Section 00XZ; Derived Categories, Tag 015F
(blueprint: lem-pe-constant-left-module-inverse-image).

The lift is characterized by its underlying-set comparison, addition and scalar
endomorphisms, and the original geometric adjunction unit. Comparisons have a
normalization equation and uniqueness; arbitrary unrelated functors are never compared.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace ConstantLeftModuleInverseImage

end ConstantLeftModuleInverseImage
open ConstantLeftModuleInverseImage

/-! The coefficient comparison is natural in the constant type. Binary operations
are compared after the isomorphism from the constant sheaf on pairs. -/
section CoefficientConstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
variable (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
variable (adj : L ⊣ R) [PreservesFiniteLimits L]

@[reassoc] private theorem constantComparison_naturality (X Y : Type u) (f : X ⟶ Y) :
    L.map ((constantSheaf J (Type u)).map f) ≫
        (constantComparison J K L R adj).hom.app Y =
      (constantComparison J K L R adj).hom.app X ≫ (constantSheaf K (Type u)).map f :=
  (constantComparison J K L R adj).hom.naturality f

variable (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]

open ConstantLeftModuleInverseImage

end CoefficientConstruction

/-! Lift left exact functors to abelian sheaves sectionwise, transport the constant
scalar endomorphisms, and extend them along ring sheafification. -/
section TransportConstruction
set_option linter.unusedSimpArgs false
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

variable {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
  {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
  (F : A ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]

section AbelianAdjunction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  [PreservesFiniteLimits L] [PreservesFiniteLimits R]
  (adj : L ⊣ R)

@[irreducible] private def abAdjunction : abInverse K J L ⊣ abDirect K J R where
  unit := abUnit K J L R adj
  counit := abCounit K J L R adj
  left_triangle_components A := by
    apply (U K).map_injective
    rw [Functor.map_comp, abCounit_forget, Functor.map_id]
    let eL := abSheafLiftSetIso K (U J ⋙ L)
    let eR := abSheafLiftSetIso J (U K ⋙ R)
    apply (cancel_mono (eL.hom.app A)).mp
    dsimp only [abCounitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_hom_app]
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      show (U K).map ((abInverse K J L).map ((abUnit K J L R adj).app A)) ≫
        (abSheafLiftSetIso K (U J ⋙ L)).hom.app
          ((abDirect K J R).obj ((abInverse K J L).obj A)) = _ from
        eL.hom.naturality ((abUnit K J L R adj).app A)]
    simp only [Category.assoc]
    simp only [Functor.comp_map]
    rw [abUnit_forget]
    dsimp only [abUnitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app]
    simp only [Functor.map_comp, Category.assoc, Functor.map_id, Category.id_comp]
    rw [← L.map_comp_assoc ((abSheafLiftSetIso J (U K ⋙ R)).inv.app _)
      ((abSheafLiftSetIso J (U K ⋙ R)).hom.app _), Iso.inv_hom_id_app,
      L.map_id, Category.id_comp]
    try simp only [Category.id_comp]
    erw [← Category.assoc (L.map (R.map ((abSheafLiftSetIso K (U J ⋙ L)).inv.app A)))
      (adj.counit.app _)]
    erw [show L.map (R.map ((abSheafLiftSetIso K (U J ⋙ L)).inv.app A)) ≫
        adj.counit.app ((U K).obj ((abInverse K J L).obj A)) =
      adj.counit.app (L.obj ((U J).obj A)) ≫
        (abSheafLiftSetIso K (U J ⋙ L)).inv.app A from
          adj.counit.naturality ((abSheafLiftSetIso K (U J ⋙ L)).inv.app A)]
    dsimp only [eL, Functor.id_obj]
    simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
    simp only [Category.assoc, adj.left_triangle_components_assoc,
      Category.comp_id, Iso.inv_hom_id_app_assoc]
    erw [Category.id_comp]
    rw [Iso.inv_hom_id_app, Category.comp_id]
  right_triangle_components A := by
    apply (U J).map_injective
    rw [Functor.map_comp, abUnit_forget, Functor.map_id]
    let eL := abSheafLiftSetIso K (U J ⋙ L)
    let eR := abSheafLiftSetIso J (U K ⋙ R)
    apply (cancel_mono (eR.hom.app A)).mp
    rw [Category.assoc, show (U J).map
      ((abDirect K J R).map ((abCounit K J L R adj).app A)) ≫ eR.hom.app A = _ from
        eR.hom.naturality ((abCounit K J L R adj).app A)]
    dsimp only [abUnitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.comp_map]
    simp only [Category.id_comp, Category.assoc]
    dsimp only [eR, Functor.comp_obj]
    rw [Iso.inv_hom_id_app_assoc]
    rw [abCounit_forget]
    dsimp only [abCounitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_hom_app]
    simp only [Functor.map_comp, Functor.map_id, Category.assoc, Category.comp_id]
    rw [← R.map_comp_assoc ((abSheafLiftSetIso K (U J ⋙ L)).inv.app _)
      ((abSheafLiftSetIso K (U J ⋙ L)).hom.app _), Iso.inv_hom_id_app,
      R.map_id, Category.id_comp]
    try simp only [R.map_id, Category.comp_id]
    erw [← Category.assoc, show adj.unit.app ((U J).obj ((abDirect K J R).obj A)) ≫
        R.map (L.map ((abSheafLiftSetIso J (U K ⋙ R)).hom.app A)) =
      (abSheafLiftSetIso J (U K ⋙ R)).hom.app A ≫ adj.unit.app _ from
        (adj.unit.naturality ((abSheafLiftSetIso J (U K ⋙ R)).hom.app A)).symm]
    try simp only [R.map_id, Category.comp_id]
    simp only [Category.assoc, R.map_id, Category.comp_id,
      adj.right_triangle_components_assoc]
    erw [R.map_id, Category.comp_id]
end AbelianAdjunction

section ModuleAction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]

variable (B : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) [B.Additive]

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def transportedModule (M : Modules J Λ) (T : Dᵒᵖ) :
    Module Λ ((B.obj ((V J Λ).obj M)).obj.obj T) where
  smul r x := (B.map (scalarEndo J Λ M r)).hom.app T x
  one_smul x := by
    change (B.map (scalarEndo J Λ M 1)).hom.app T x = x
    simp only [scalarEndo_one, Functor.map_id]
    rfl
  zero_smul x := by
    change (B.map (scalarEndo J Λ M 0)).hom.app T x = 0
    simp only [scalarEndo_zero, Functor.map_zero]
    rfl
  smul_zero r := (B.map (scalarEndo J Λ M r)).hom.app T |>.hom.map_zero
  smul_add r x y := (B.map (scalarEndo J Λ M r)).hom.app T |>.hom.map_add x y
  add_smul r s x := by
    change (B.map (scalarEndo J Λ M (r + s))).hom.app T x =
      (B.map (scalarEndo J Λ M r)).hom.app T x +
        (B.map (scalarEndo J Λ M s)).hom.app T x
    simp only [scalarEndo_add, B.map_add]
    rfl
  mul_smul r s x := by
    change (B.map (scalarEndo J Λ M (r * s))).hom.app T x =
      (B.map (scalarEndo J Λ M r)).hom.app T
        ((B.map (scalarEndo J Λ M s)).hom.app T x)
    simp only [scalarEndo_mul, B.map_comp]
    rfl

variable [HasWeakSheafify K RingCat.{u}]
  (B' : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}) [B'.Additive]
  (a : B ⊣ B')

@[irreducible] private def moduleAdjunction :
    transportedModuleFunctor K J Λ B ⊣ transportedModuleFunctor J K Λ B' where
  unit := moduleUnit K J Λ B B' a
  counit := moduleCounit K J Λ B B' a
  left_triangle_components M := by
    apply (V K Λ).map_injective
    change B.map (a.unit.app ((V J Λ).obj M)) ≫
      a.counit.app (B.obj ((V J Λ).obj M)) = 𝟙 _
    exact a.left_triangle_components _
  right_triangle_components M := by
    apply (V J Λ).map_injective
    change a.unit.app (B'.obj ((V K Λ).obj M)) ≫
      B'.map (a.counit.app ((V K Λ).obj M)) = 𝟙 _
    exact a.right_triangle_components _

end ModuleAction
section Assembly
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]
  (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : L ⊣ R) (hL : PreservesFiniteLimits L)

end Assembly

end TransportConstruction

end CategoryTheory
