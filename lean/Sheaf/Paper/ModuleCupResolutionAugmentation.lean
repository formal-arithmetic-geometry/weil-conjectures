/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ModuleCupRealizationComplexData
public import Sheaf.Paper.ModuleCupCanonicalHZeroIdentification

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

/-- A realization respects the coefficient augmentations before localization.
Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-augmentation)
Proof: the source tensor of single complexes is concentrated in degree zero. In all
other degrees both maps vanish. In degree zero, test the maps on elementary tensors
of sections over each open. The extension/single and tensor/single isomorphisms send
these tensors to the corresponding degree-zero summand. Apply Realizes at p=q=0,
then augmentation_pair. Elementary tensors generate the presheaf tensor and hence
its sheafification, so equality on these sections gives equality of sheaf morphisms.
Degreewise extensionality gives the cochain identity. -/
theorem moduleCup_resolution_augmentation {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t) :
    (CategoryTheory.MonoidalCategory.tensorHom
      (C := CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
        HomologicalComplex.extendMap D.left.augmentation ComplexShape.embeddingUpNat)
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv ≫
        HomologicalComplex.extendMap D.right.augmentation ComplexShape.embeddingUpNat)) ≫ t =
      (DerivedCategory.moduleCup_singleTensorIso
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) F G).hom ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (F ⊗ G) 0 0 rfl).inv ≫
        HomologicalComplex.extendMap D.target.augmentation ComplexShape.embeddingUpNat := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
