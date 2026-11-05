/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
set_option linter.privateModule false  -- prune: only private declarations remain

/-! # Tensor cancellation for extension of scalars of internal modules

Source: Stacks Tag 07A4, the balanced tensor cancellation in change of rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory MonObj Limits BraidedCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

set_option backward.isDefEq.respectTransparency false in
private def restrictRight {A : Mon C} (P : Bimod A (Mon.mk S)) :
    Bimod A (Mon.mk R) where
  X := P.X
  actLeft := P.actLeft
  actRight := P.X ◁ φ ≫ P.actRight
  one_actLeft := P.one_actLeft
  actRight_one := by
    rw [← whiskerLeft_comp_assoc, IsMonHom.one_hom, P.actRight_one]
  left_assoc := P.left_assoc
  right_assoc := by
    change P.X ◁ μ[R] ≫ P.X ◁ φ ≫ P.actRight =
      (α_ P.X R R).inv ≫ (P.X ◁ φ ≫ P.actRight) ▷ R ≫ P.X ◁ φ ≫ P.actRight
    rw [← whiskerLeft_comp_assoc, IsMonHom.mul_hom, whiskerLeft_comp_assoc,
      P.right_assoc]
    simp only [MonoidalCategory.tensorHom_def, whiskerLeft_comp,
      comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
      whisker_exchange_assoc]
  middle_assoc := by
    rw [← whisker_exchange_assoc, P.middle_assoc, whiskerLeft_comp_assoc,
      associator_naturality_right_assoc]

private def bimodForget (A B : Mon C) : Bimod A B ⥤ C where
  obj P := P.X
  map f := f.hom

set_option backward.isDefEq.respectTransparency false in
private def restrictRightUnitIso {A : Mon C} (P : Bimod A (Mon.mk S)) :
    P.tensorBimod (Bimod.ofMonHom φ) ≅ restrictRight φ P :=
  Bimod.isoOfIso
    { hom := Bimod.RightUnitorBimod.hom P
      inv := Bimod.RightUnitorBimod.inv P
      hom_inv_id := Bimod.RightUnitorBimod.hom_inv_id P
      inv_hom_id := Bimod.RightUnitorBimod.inv_hom_id P }
    (Bimod.RightUnitorBimod.hom_left_act_hom' P) (by
      let q := coequalizer.π (P.actRight ▷ (Bimod.ofMonHom φ).X)
        ((α_ P.X S (Bimod.ofMonHom φ).X).hom ≫ P.X ◁ (Bimod.ofMonHom φ).actLeft)
      have : Epi (q ▷ R) := (tensorRight R).map_epi q
      apply (cancel_epi (q ▷ R)).1
      dsimp only [q]
      erw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight P (Bimod.ofMonHom φ)]
      change (α_ P.X S R).hom ≫ P.X ◁ (S ◁ φ ≫ μ[S]) ≫
        coequalizer.π _ _ ≫ Bimod.RightUnitorBimod.hom P =
        coequalizer.π _ _ ▷ R ≫ Bimod.RightUnitorBimod.hom P ▷ R ≫
          P.X ◁ φ ≫ P.actRight
      rw [← comp_whiskerRight_assoc]
      dsimp only [Bimod.RightUnitorBimod.hom]
      erw [coequalizer.π_desc]
      rw [whiskerLeft_comp_assoc, P.right_assoc,
        associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
        whisker_exchange_assoc])

private def bimodTensorRight {A B D : Mon C} (N : Bimod B D) :
    Bimod A B ⥤ Bimod A D where
  obj P := P.tensorBimod N
  map f := Bimod.whiskerRight f N
  map_id _P := Bimod.id_whiskerRight_bimod
  map_comp f g := Bimod.comp_whiskerRight_bimod f g N

private def cancellationBimodIso (M : Mod C R) {A : Mon C}
    (P : Bimod A (Mon.mk S)) :
    P.tensorBimod (extendScalarsBimod φ M) ≅
      (restrictRight φ P).tensorBimod (toBimodObj R M) :=
  (Bimod.associatorBimod P (Bimod.ofMonHom φ) (toBimodObj R M)).symm ≪≫
    (bimodTensorRight (toBimodObj R M)).mapIso (restrictRightUnitIso φ P)

section Flat

variable [Abelian C]

attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits

end Flat

end CategoryTheory.Mod
