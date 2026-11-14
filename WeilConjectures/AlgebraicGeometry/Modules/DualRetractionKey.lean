/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Categorical cancellation for the local transpose retraction.
Source: Stacks Project, Tag 0EKP, transpose compatibility.

The naturality hypothesis rewrites the restricted transpose as local precomposition.
Contravariant functoriality of `homObjMap` combines this with precomposition by `s`.
The section equation `hs` makes that map the identity; the isomorphism cancels.
Naturality is essential: arbitrary unrelated isomorphisms do not satisfy this equation. -/
theorem dual_retraction_key
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) (U : X.Opens)
    (s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P)
    (e : ∀ A B : X.Modules,
      (restrictFunctor U.ι).obj (SheafOfModules.homObj
        (R := X.sheaf) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf)
          ((restrictFunctor U.ι).obj A) ((restrictFunctor U.ι).obj B))
    (he : ∀ {A A' B B' : X.Modules} (a : A' ⟶ A) (b : B ⟶ B'),
      (restrictFunctor U.ι).map
          (SheafOfModules.homObjMap (R := X.sheaf) a b) ≫
        (e A' B').hom = (e A B).hom ≫
          SheafOfModules.homObjMap (R := U.toScheme.sheaf)
            ((restrictFunctor U.ι).map a) ((restrictFunctor U.ι).map b))
    (hs : s ≫ (restrictFunctor U.ι).map f = 𝟙 _) :
    (restrictFunctor U.ι).map (dualMap f) ≫
        (e P (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          s (𝟙 _) ≫ (e Q (SheafOfModules.unit X.ringCatSheaf)).inv = 𝟙 _ := by
  let N := (restrictFunctor U.ι).obj (SheafOfModules.unit X.ringCatSheaf)
  have h : (restrictFunctor U.ι).map (dualMap f) ≫
      (e P (SheafOfModules.unit X.ringCatSheaf)).hom =
      (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          ((restrictFunctor U.ι).map f) (𝟙 N) := by
    exact (he f (𝟙 (SheafOfModules.unit X.ringCatSheaf))).trans
      (congrArg (fun b => (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          ((restrictFunctor U.ι).map f) b)
        ((restrictFunctor U.ι).map_id (SheafOfModules.unit X.ringCatSheaf)))
  have hc : SheafOfModules.homObjMap (R := U.toScheme.sheaf)
      ((restrictFunctor U.ι).map f) (𝟙 N) ≫
      SheafOfModules.homObjMap (R := U.toScheme.sheaf) s (𝟙 N) = 𝟙 _ :=
    (SheafOfModules.homObjMap_comp_homObjMap (R := U.toScheme.sheaf)
      ((restrictFunctor U.ι).map f) s (𝟙 N) (𝟙 N)).trans
      ((congrArg₂ (fun a b => SheafOfModules.homObjMap (R := U.toScheme.sheaf) a b)
        hs (Category.id_comp _)).trans
        (SheafOfModules.homObjMap_id (R := U.toScheme.sheaf)))
  calc
    _ = ((restrictFunctor U.ι).map (dualMap f) ≫
        (e P (SheafOfModules.unit X.ringCatSheaf)).hom) ≫
        (SheafOfModules.homObjMap (R := U.toScheme.sheaf) s (𝟙 N) ≫
          (e Q (SheafOfModules.unit X.ringCatSheaf)).inv) :=
      (Category.assoc _ _ _).symm
    _ = ((e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          ((restrictFunctor U.ι).map f) (𝟙 N)) ≫ _ := congrArg (fun a => a ≫ _) h
    _ = (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        ((SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          ((restrictFunctor U.ι).map f) (𝟙 N) ≫
          SheafOfModules.homObjMap (R := U.toScheme.sheaf) s (𝟙 N)) ≫
            (e Q (SheafOfModules.unit X.ringCatSheaf)).inv) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫ a)
          (Category.assoc _ _ _).symm)
    _ = (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (𝟙 _ ≫ (e Q (SheafOfModules.unit X.ringCatSheaf)).inv) :=
      congrArg (fun a => (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (a ≫ (e Q (SheafOfModules.unit X.ringCatSheaf)).inv)) hc
    _ = _ := (congrArg (fun a => (e Q (SheafOfModules.unit X.ringCatSheaf)).hom ≫ a)
        (Category.id_comp _)).trans (e Q (SheafOfModules.unit X.ringCatSheaf)).hom_inv_id

end AlgebraicGeometry.Scheme.Modules
