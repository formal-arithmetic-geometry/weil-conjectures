/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Transporting a monoidal structure onto a prescribed tensor bifunctor 
(blueprint: lem-pur-u2-prescribed-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory
namespace CategoryTheory.Monoidal
variable {A : Type*} [Category* A] [m : MonoidalCategory A]
  (T : A × A ⥤ A) (e : Functor.uncurry.obj (curriedTensor A) ≅ T)

/-- Naturality on a pair of morphisms.
Source: naturality of the given tensor isomorphism.
(blueprint: lem-pur-u2-prescribed-tensor). -/
theorem tensor_naturality {X Y X' Y' : A} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ e.hom.app (Y, Y') = e.hom.app (X, X') ≫ T.map (f, g) := by
  have h := e.hom.naturality (X := (X, X')) (Y := (Y, Y')) (f, g)
  change (f ▷ X' ≫ Y ◁ g) ≫ _ = _ at h
  rw [← tensorHom_def] at h
  exact h

/-- The constraints obtained by conjugating the original constraints by `e`.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensorStruct : MonoidalCategoryStruct A where
  tensorObj X Y := T.obj (X, Y)
  whiskerLeft X _ _ f := T.map (𝟙 X, f)
  whiskerRight f Y := T.map (f, 𝟙 Y)
  tensorHom f g := T.map (f, g)
  tensorUnit := 𝟙_ A
  associator X Y Z :=
    (e.app (T.obj (X, Y), Z)).symm ≪≫
      ((e.app (X, Y)).symm ⊗ᵢ Iso.refl Z) ≪≫ α_ X Y Z ≪≫
      (Iso.refl X ⊗ᵢ e.app (Y, Z)) ≪≫ e.app (X, T.obj (Y, Z))
  leftUnitor X := (e.app (𝟙_ A, X)).symm ≪≫ λ_ X
  rightUnitor X := (e.app (X, 𝟙_ A)).symm ≪≫ ρ_ X

/-- The identity functor identifies the conjugated tensor with the original tensor.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
def prescribedTensorInducing :
    @InducingFunctorData A _ m A _ (prescribedTensorStruct T e) (𝟭 A) := by
  refine @InducingFunctorData.mk A _ m A _ (prescribedTensorStruct T e) (𝟭 A)
    (fun X Y ↦ e.app (X, Y)) ?_ ?_ ?_ (Iso.refl _) ?_ ?_ ?_
  · intro X Y Y' f
    change T.map (𝟙 X, f) = (e.app (X, Y)).inv ≫
      @whiskerLeft A _ m.toMonoidalCategoryStruct X Y Y' f ≫ (e.app (X, Y')).hom
    apply (cancel_epi (e.app (X, Y)).hom).1
    rw [Iso.hom_inv_id_assoc]
    simpa only [Iso.app_hom, @id_tensorHom A _ m] using (tensor_naturality T e (𝟙 X) f).symm
  · intro X X' f Y
    change T.map (f, 𝟙 Y) = (e.app (X, Y)).inv ≫
      @whiskerRight A _ m.toMonoidalCategoryStruct X X' f Y ≫ (e.app (X', Y)).hom
    apply (cancel_epi (e.app (X, Y)).hom).1
    rw [Iso.hom_inv_id_assoc]
    simpa only [Iso.app_hom, @tensorHom_id A _ m] using (tensor_naturality T e f (𝟙 Y)).symm
  · intro X Y X' Y' f g
    change T.map (f, g) = (e.app (X, X')).inv ≫
      @tensorHom A _ m.toMonoidalCategoryStruct X Y X' Y' f g ≫ (e.app (Y, Y')).hom
    apply (cancel_epi (e.app (X, X')).hom).1
    rw [Iso.hom_inv_id_assoc]
    simpa only [Iso.app_hom] using (tensor_naturality T e f g).symm
  · intro X Y Z
    dsimp only [associator, tensorObj, prescribedTensorStruct, Functor.id_map,
      Functor.id_obj]
    change ((e.app (T.obj (X, Y), Z)).symm ≪≫
      ((e.app (X, Y)).symm ⊗ᵢ Iso.refl Z) ≪≫ α_ X Y Z ≪≫
      (Iso.refl X ⊗ᵢ e.app (Y, Z)) ≪≫ e.app (X, T.obj (Y, Z))).hom = _
    simp only [Iso.trans_hom, Category.assoc]
  · intro X
    dsimp only [leftUnitor, rightUnitor, tensorUnit, prescribedTensorStruct,
      Functor.id_map, Functor.id_obj]
    change (e.app (𝟙_ A, X)).inv ≫ (λ_ X).hom = _
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      Iso.refl_inv, @tensorHom_id A _ m, @id_whiskerRight A _ m, Category.id_comp,
      Category.assoc]
  · intro X
    dsimp only [leftUnitor, rightUnitor, tensorUnit, prescribedTensorStruct,
      Functor.id_map, Functor.id_obj]
    change (e.app (X, 𝟙_ A)).inv ≫ (ρ_ X).hom = _
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      Iso.refl_inv, @tensorHom_id A _ m, @id_whiskerRight A _ m, Category.id_comp,
      Category.assoc]

/-- The monoidal structure with the prescribed tensor.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensor : MonoidalCategory A :=
  letI := prescribedTensorStruct T e
  induced (𝟭 A) (prescribedTensorInducing T e)

/-- The induced tensor bifunctor is exactly the prescribed bifunctor.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
theorem prescribedTensor_eq :
    letI := prescribedTensor T e
    Functor.uncurry.obj (curriedTensor A) = T := by
  let := prescribedTensor T e
  apply Functor.ext
  · intro X Y f
    dsimp only [Functor.uncurry, curriedTensor, prescribedTensor, induced,
      prescribedTensorStruct]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change T.map (X := X) (Y := (Y.1, X.2)) (f.1, 𝟙 X.2) ≫
      T.map (X := (Y.1, X.2)) (Y := Y) (𝟙 Y.1, f.2) = T.map f
    rw [← T.map_comp]
    congr 1
    ext <;> simp
  · intro X
    rfl

/-- The comparison identity functor is strong monoidal.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensorMonoidal :
    @Functor.Monoidal A _ (prescribedTensor T e) A _ m (𝟭 A) :=
  @fromInducedMonoidal A _ m A _ (prescribedTensorStruct T e) (𝟭 A) inferInstance
    (prescribedTensorInducing T e)

/-- Symmetry transports along the same comparison identity functor.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensorSymmetric [SymmetricCategory A] :
    @SymmetricCategory A _ (prescribedTensor T e) :=
  @SymmetricCategory.ofFullyFaithful A A _ _ (prescribedTensor T e) m (𝟭 A)
    (prescribedTensorMonoidal T e) inferInstance inferInstance inferInstance

/-- The identity equivalence between the two tensor structures.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
def prescribedTensorEquivalence : A ≌ A := Equivalence.refl

/-- The tensor transport in the forward direction.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensorForward :
    @Functor.Monoidal A _ m A _ (prescribedTensor T e) (𝟭 A) := by
  let E : A ≌ A := prescribedTensorEquivalence (A := A)
  letI : @Functor.Monoidal A _ (prescribedTensor T e) A _ m E.functor :=
    prescribedTensorMonoidal T e
  exact @Equivalence.inverseMonoidal A _ (prescribedTensor T e) A _ m E inferInstance

end CategoryTheory.Monoidal

namespace CategoryTheory
/-- The symmetric structure pulled back along a fully faithful monoidal functor makes
that functor braided.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def symmetricFullyFaithfulBraided {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] [SymmetricCategory B]
    (F : A ⥤ B) [F.Monoidal] [F.Full] [F.Faithful] :
    letI := SymmetricCategory.ofFullyFaithful F
    F.Braided := by
  letI := SymmetricCategory.ofFullyFaithful F
  refine { toMonoidal := inferInstance, braided := ?_ }
  intro X Y
  change Functor.LaxMonoidal.μ F X Y ≫
    F.map (F.preimageIso
      ((Functor.Monoidal.μIso F X Y).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫
        Functor.Monoidal.μIso F Y X)).hom = _
  dsimp only [Functor.preimageIso]
  rw [Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μIso_inv, Functor.Monoidal.μ_δ_assoc]
/-- A braided monoidal equivalence has a braided monoidal inverse.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def braidedInverse {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
    (E : A ≌ B) [E.functor.Braided] :
    letI := E.inverseMonoidal
    E.inverse.Braided := by
  letI := E.inverseMonoidal
  have : E.IsMonoidal := inferInstance
  refine { toMonoidal := inferInstance, braided := ?_ }
  intro X Y
  apply E.functor.map_injective
  apply (cancel_epi (Functor.LaxMonoidal.μ E.functor (E.inverse.obj X) (E.inverse.obj Y))).1
  have : NatTrans.IsMonoidal E.counitIso.hom := inferInstance
  have : NatTrans.IsMonoidal E.counitIso.inv := inferInstance
  have : NatTrans.IsMonoidal E.counitIso.symm.hom := by
    change NatTrans.IsMonoidal E.counitIso.inv
    infer_instance
  let lb : (E.inverse ⋙ E.functor).LaxBraided :=
    Functor.LaxBraided.ofNatIso E.counitIso.symm
  have h := lb.braided X Y
  change (Functor.LaxMonoidal.μ E.functor (E.inverse.obj X) (E.inverse.obj Y) ≫
    E.functor.map (Functor.LaxMonoidal.μ E.inverse X Y)) ≫
    E.functor.map (E.inverse.map (β_ X Y).hom) = _ at h
  simp only [Functor.map_comp]
  rw [Functor.LaxBraided.braided_assoc (F := E.functor)]
  simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Category.assoc] using h
end CategoryTheory

namespace CategoryTheory.Monoidal
variable {A : Type*} [Category* A] [m : MonoidalCategory A]
  (T : A × A ⥤ A) (e : Functor.uncurry.obj (curriedTensor A) ≅ T)
/-- The comparison to the original symmetric category is braided.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensorBackwardBraided [b : SymmetricCategory A] :
    @Functor.Braided A _ (prescribedTensor T e)
      (prescribedTensorSymmetric T e).toBraidedCategory A _ m b.toBraidedCategory (𝟭 A) :=
  @symmetricFullyFaithfulBraided A A _ _ (prescribedTensor T e) m b (𝟭 A)
    (prescribedTensorMonoidal T e) inferInstance inferInstance
/-- The comparison from the original symmetric category is braided.
Source: Mathlib.CategoryTheory.Monoidal.Transport; Mathlib.CategoryTheory.Monoidal.Braided.Basic;
Monoidal.induced, fromInducedMonoidal, SymmetricCategory.ofFullyFaithful; explicit conjugation of
constraints.
(blueprint: lem-pur-u2-prescribed-tensor). -/
@[instance_reducible]
def prescribedTensorForwardBraided [b : SymmetricCategory A] :
    @Functor.Braided A _ m b.toBraidedCategory A _ (prescribedTensor T e)
      (prescribedTensorSymmetric T e).toBraidedCategory (𝟭 A) := by
  let E : A ≌ A := prescribedTensorEquivalence (A := A)
  letI : @Functor.Braided A _ (prescribedTensor T e)
      (prescribedTensorSymmetric T e).toBraidedCategory A _ m b.toBraidedCategory E.functor :=
    prescribedTensorBackwardBraided T e
  exact @braidedInverse A A _ _ (prescribedTensor T e) m
    (prescribedTensorSymmetric T e).toBraidedCategory b.toBraidedCategory E inferInstance
end CategoryTheory.Monoidal
