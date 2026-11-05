/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Transport and normalization of tensor representatives
Source: Stacks 0FPT, 06YU and 07A4.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.MonoidalCategory
namespace WeilConjectures
attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  coefficientTotalTensor coefficientKFlatInclusion
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTensorGenerator
  CoefficientTensorModels.iso DerivedCategory.Q
section CoherenceTransfer

universe a b x y
variable {D : Type a} [Category.{x} D] {E' : Type b} [Category.{y} E']
  {H : Dᵒᵖ × D ⥤ D} {HU : E'ᵒᵖ × E' ⥤ E'}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  {r : D ⥤ E'}
variable (rho : ∀ L M : D, r.obj (S.tensor.obj (L, M)) ≅
    SU.tensor.obj (r.obj L, r.obj M))
  (rho_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    r.map (S.tensor.map (f, g)) ≫ (rho L' M').hom =
      (rho L M).hom ≫ SU.tensor.map (r.map f, r.map g))
include rho rho_naturality

-- The concrete site and tensor instances require additional elaboration heartbeats.
section RepresentativeComparison
universe a' b' x' y'
variable {V : Type a'} [Category.{x'} V] {W : Type b'} [Category.{y'} W]

end RepresentativeComparison
end CoherenceTransfer

section ModelNaturality
universe c v r d
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{d} (RingedTensorModules.{c, v, r} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, d} J R))
  (T : CoefficientTensorModels.{r, c, v, d} J R S)

end ModelNaturality
end WeilConjectures
