/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # The termwise section tensor map

Source: Stacks, Section 20.31 (Tag 0FKU), the naive cup before Lemma 20.31.3.
The degree maps are coproduct descents of tensorSectionsMap followed by the
sheaf tensor summand inclusions. A named chain identity supplies the proof
component of the actual cochain map; all its data is constructed explicitly.
-/

@[expose] public section

universe u wC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})

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
/-- Tensor sections, as a morphism of global-section modules.
Source: Stacks, Tag 0FKU (blueprint: lem-sc-module-cup-naive-map-chain). -/
def moduleCup_sectionTensorMap (M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (M ⊗ N) :=
  ModuleCat.ofHom (tensorSectionsMap M N ⊤)

/-- The section tensor map in degree n, constructed by the total tensor coproduct.
Source: Stacks, Tag 0FKU, the naive product before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-naive-map-chain) -/
def moduleCup_naiveMapComponent
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) :
    ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) ⊗
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)).X n ⟶
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (K ⊗ L) |>.X n :=
  HomologicalComplex.mapBifunctorDesc (fun i j h ↦
    moduleCup_sectionTensorMap X (K.X i) (L.X j) ≫
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
        (HomologicalComplex.ιTensorObj K L i j n h))

/-- The summandwise section tensor maps commute with the total differentials.
Source: Stacks, Tag 0FKU, the naive product before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-naive-map-chain)
Proof: precompose both sides with every (i,j)-summand inclusion. The total
 differential is the sum of the differential in the first factor and the signed
 differential in the second factor. Tensor sections commute with each factor's
 morphism by tensorHom_app_tmulSection. Sections is additive, so it preserves
 the sum and the integer sign. Thus both sides agree on pure tensors in each
 summand. TensorProduct.ext and the coproduct universal property give equality.
This uses all integer degrees, including negative ones, without boundedness. -/
theorem moduleCup_naiveMap_comm
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n m : ℤ) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    (T.obj K ⊗ T.obj L).d n m ≫ moduleCup_naiveMapComponent X K L m =
      moduleCup_naiveMapComponent X K L n ≫ (T.obj (K ⊗ L)).d n m := by sorry

/-- The actual naive section tensor cochain map.
Source: Stacks, Tag 0FKU, the naive product before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-naive-map-chain) -/
def moduleCup_naiveMap
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L) where
  f := moduleCup_naiveMapComponent X K L
  comm' := fun n m _ ↦ (moduleCup_naiveMap_comm X K L n m).symm

/-- The explicit naive map tensors sections on every coproduct summand. -/
theorem moduleCup_naiveMap_summand
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i j n : ℤ) (h : i + j = n) (x : Γ(K.X i, ⊤)) (y : Γ(L.X j, ⊤)) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ((moduleCup_naiveMap X K L).f n).hom
        ((HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h).hom
          (TensorProduct.tmul Γ(X, ⊤) x y)) =
      (HomologicalComplex.ιTensorObj K L i j n h).val.app (op ⊤)
        (tmulSection x y) := by
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have e := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := T.obj K) (K₂ := T.obj L) (F := curriedTensor _) (c := ComplexShape.up ℤ)
    (fun a b hab ↦
      (show (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (K.X a) ⊗
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (L.X b) ⟶
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (K.X a ⊗ L.X b) from
        ModuleCat.ofHom (tensorSectionsMap (K.X a) (L.X b) ⊤)) ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
          (HomologicalComplex.ιTensorObj K L a b n hab)) i j h
  exact congrArg (fun f ↦ f.hom (TensorProduct.tmul Γ(X, ⊤) x y)) e


end
end AlgebraicGeometry.Scheme.Modules
