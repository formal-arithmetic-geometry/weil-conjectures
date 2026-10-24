/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The tensor product of a full monoidal subcategory commutes with the shifts

Let `P` be a full monoidal subcategory of a monoidal category `C` with a shift, stable under the
shift. If `K ⊗ -` (resp. `- ⊗ K`) commutes with the shifts on `C`, so does `K ⊗ -` (resp.
`- ⊗ K`) on `P` (`ObjectProperty.commShiftTensorLeft`, `ObjectProperty.commShiftTensorRight`):
it is the functor induced by the ambient one (`ObjectProperty.tensorLeftIsoLift`), and its
commutation isomorphisms are those of `C` (`ObjectProperty.ι_map_commShiftIso_tensorLeft_hom_app`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
  {A : Type*} [AddMonoid A] [HasShift C A] [P.IsStableUnderShift A]

/-- The functor `K ⊗ -` on `P` is the functor induced by `K ⊗ -` on `C`. -/
def tensorLeftIsoLift (K : P.FullSubcategory) :
    P.liftFullSubcategory P ((curriedTensor C).obj K.obj) (fun _ hX ↦ P.prop_tensor K.2 hX) ≅
      (curriedTensor P.FullSubcategory).obj K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    ext
    simp)

/-- The functor `- ⊗ K` on `P` is the functor induced by `- ⊗ K` on `C`. -/
def tensorRightIsoLift (K : P.FullSubcategory) :
    P.liftFullSubcategory P ((curriedTensor C).flip.obj K.obj) (fun _ hX ↦ P.prop_tensor hX K.2) ≅
      (curriedTensor P.FullSubcategory).flip.obj K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    ext
    simp)

/-- The functor `K ⊗ -` on `P` commutes with the shifts. -/
noncomputable instance commShiftTensorLeft (K : P.FullSubcategory)
    [((curriedTensor C).obj K.obj).CommShift A] :
    ((curriedTensor P.FullSubcategory).obj K).CommShift A :=
  Functor.CommShift.ofIso (P.tensorLeftIsoLift K) A

/-- The functor `- ⊗ K` on `P` commutes with the shifts. -/
noncomputable instance commShiftTensorRight (K : P.FullSubcategory)
    [((curriedTensor C).flip.obj K.obj).CommShift A] :
    ((curriedTensor P.FullSubcategory).flip.obj K).CommShift A :=
  Functor.CommShift.ofIso (P.tensorRightIsoLift K) A

/-- The functor `K ⊗ -` on `P` is compatible with `K ⊗ -` on `C` through the inclusion. -/
def tensorLeftCompιIso (K : P.FullSubcategory) :
    (curriedTensor P.FullSubcategory).obj K ⋙ P.ι ≅ P.ι ⋙ (curriedTensor C).obj K.obj :=
  Functor.isoWhiskerRight (P.tensorLeftIsoLift K).symm P.ι ≪≫
    P.liftFullSubcategoryCompιIso P _ (fun _ hX ↦ P.prop_tensor K.2 hX)

/-- The functor `- ⊗ K` on `P` is compatible with `- ⊗ K` on `C` through the inclusion. -/
def tensorRightCompιIso (K : P.FullSubcategory) :
    (curriedTensor P.FullSubcategory).flip.obj K ⋙ P.ι ≅ P.ι ⋙ (curriedTensor C).flip.obj K.obj :=
  Functor.isoWhiskerRight (P.tensorRightIsoLift K).symm P.ι ≪≫
    P.liftFullSubcategoryCompιIso P _ (fun _ hX ↦ P.prop_tensor hX K.2)

/-- The commutation of `K ⊗ -` on `P` with the shifts is that of `K ⊗ -` on `C`. -/
instance commShift_tensorLeftCompιIso_hom (K : P.FullSubcategory)
    [((curriedTensor C).obj K.obj).CommShift A] :
    NatTrans.CommShift (P.tensorLeftCompιIso K).hom A := by
  have : NatTrans.CommShift (P.tensorLeftIsoLift K).hom A :=
    Functor.CommShift.ofIso_compatibility _ _
  have : NatTrans.CommShift (P.tensorLeftIsoLift K).symm.hom A :=
    NatTrans.CommShift.of_iso_inv (P.tensorLeftIsoLift K) A
  dsimp only [tensorLeftCompιIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The commutation of `- ⊗ K` on `P` with the shifts is that of `- ⊗ K` on `C`. -/
instance commShift_tensorRightCompιIso_hom (K : P.FullSubcategory)
    [((curriedTensor C).flip.obj K.obj).CommShift A] :
    NatTrans.CommShift (P.tensorRightCompιIso K).hom A := by
  have : NatTrans.CommShift (P.tensorRightIsoLift K).hom A :=
    Functor.CommShift.ofIso_compatibility _ _
  have : NatTrans.CommShift (P.tensorRightIsoLift K).symm.hom A :=
    NatTrans.CommShift.of_iso_inv (P.tensorRightIsoLift K) A
  dsimp only [tensorRightCompιIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

end CategoryTheory.ObjectProperty
