/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.CompletedTensorUnitInsertionData
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Multifunctor
import all Sheaf.CategoryTheory.BraidedSheafTensorGenerators

/-! # Symmetric monoidal structure of a tensor-compatible reflector -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe uB vB uE vE u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.ConstantCompletion


variable {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [SymmetricCategory B]

private abbrev reflector (P : ObjectProperty B) (T : B ⥤ B)
    (hT : ∀ X : B, P (T.obj X)) : B ⥤ P.FullSubcategory := ObjectProperty.lift P T hT

private def reflectorAdjunction
    (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hT : ∀ X : B, P (T.obj X))
    (hbij : ∀ (X Z : B), P Z →
      Function.Bijective (fun f : T.obj X ⟶ Z ↦ η.app X ≫ f)) :
    reflector P T hT ⊣ P.ι := by
  let e (X : B) (Z : P.FullSubcategory) :
      ((reflector P T hT).obj X ⟶ Z) ≃ (X ⟶ Z.obj) :=
    P.fullyFaithfulι.homEquiv.trans (Equiv.ofBijective _ (hbij X Z.obj Z.property))
  refine Adjunction.mkOfHomEquiv {
    homEquiv := e
    homEquiv_naturality_left_symm := ?_
    homEquiv_naturality_right := ?_ }
  · intro X' X Z f g
    have he (U : B) (V : P.FullSubcategory) (k : U ⟶ V.obj) :
        η.app U ≫ ((e U V).symm k).hom = k := (e U V).apply_symm_apply k
    apply P.fullyFaithfulι.map_injective
    apply (hbij X' Z.obj Z.property).injective
    change η.app X' ≫ ((e X' Z).symm (f ≫ g)).hom =
      η.app X' ≫ T.map f ≫ ((e X Z).symm g).hom
    rw [he, ← η.naturality_assoc, he]
    rfl
  · intro X Z Z' f g
    exact (Category.assoc _ _ _).symm

private theorem reflector_monoidalEquivalences
    (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hT : ∀ X : B, P (T.obj X))
    (hLeft : ∀ X W : B, IsIso (tensorInsertLeft T η X W)) :
    ((MorphismProperty.isomorphisms P.FullSubcategory).inverseImage
      (reflector P T hT)).IsMonoidal := by
  let W := (MorphismProperty.isomorphisms P.FullSubcategory).inverseImage
    (reflector P T hT)
  have hleft {X Y : B} (f : X ⟶ Y) (hf : W f) (Z : B) : W (f ▷ Z) := by
    have hi : IsIso (T.map f) := by
      exact (ObjectProperty.isIso_hom_iff ((reflector P T hT).map f)).2 hf
    have hX : IsIso (T.map (η.app X ⊗ₘ 𝟙 Z)) := hLeft X Z
    have hY : IsIso (T.map (η.app Y ⊗ₘ 𝟙 Z)) := hLeft Y Z
    have h : T.map (f ⊗ₘ 𝟙 Z) ≫ T.map (η.app Y ⊗ₘ 𝟙 Z) =
        T.map (η.app X ⊗ₘ 𝟙 Z) ≫ T.map (T.map f ⊗ₘ 𝟙 Z) := by
      rw [← T.map_comp, ← T.map_comp]
      congr 1
      simp only [tensorHom_comp_tensorHom, Category.comp_id]
      exact congrArg (fun a ↦ a ⊗ₘ 𝟙 Z) (η.naturality f)
    have : IsIso (T.map (f ⊗ₘ 𝟙 Z) ≫ T.map (η.app Y ⊗ₘ 𝟙 Z)) := by
      rw [h]
      infer_instance
    have : IsIso (T.map (f ⊗ₘ 𝟙 Z)) :=
      IsIso.of_isIso_comp_right _ (T.map (η.app Y ⊗ₘ 𝟙 Z))
    apply (ObjectProperty.isIso_hom_iff ((reflector P T hT).map (f ▷ Z))).1
    change IsIso (T.map (f ▷ Z))
    simpa only [tensorHom_id] using this
  exact {
    whiskerRight := fun f hf Z ↦ hleft f hf Z
    whiskerLeft := by
      intro Z X Y f hf
      have h : Z ◁ f = (β_ Z X).hom ≫ (f ▷ Z) ≫ (β_ Y Z).hom := by
        rw [← tensorHom_id, ← id_tensorHom, ← BraidedCategory.braiding_naturality_assoc]
        simp only [SymmetricCategory.symmetry, Category.comp_id]
      have : IsIso ((reflector P T hT).map (f ▷ Z)) := hleft f hf Z
      change IsIso ((reflector P T hT).map (Z ◁ f))
      rw [h, Functor.map_comp, Functor.map_comp]
      infer_instance }

omit [SymmetricCategory B] in
private theorem right_unit_counit
    {D : Type*} [Category D] [MonoidalCategory D]
    (F : B ⥤ D) [F.OplaxMonoidal] {X : B} {Y : D} (f : F.obj X ⟶ Y) :
    Functor.OplaxMonoidal.δ F X (𝟙_ B) ≫
      (f ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (ρ_ Y).hom =
      F.map (ρ_ X).hom ≫ f := by
  simp only [tensorHom_def, Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ f) (Functor.OplaxMonoidal.right_unitality_hom F X)

omit [SymmetricCategory B] in
private theorem left_unit_counit
    {D : Type*} [Category D] [MonoidalCategory D]
    (F : B ⥤ D) [F.OplaxMonoidal] {X : B} {Y : D} (f : F.obj X ⟶ Y) :
    Functor.OplaxMonoidal.δ F (𝟙_ B) X ≫
      (Functor.OplaxMonoidal.η F ⊗ₘ f) ≫ (λ_ Y).hom =
      F.map (λ_ X).hom ≫ f := by
  simp only [tensorHom_def', Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ f) (Functor.OplaxMonoidal.left_unitality_hom F X)

omit [SymmetricCategory B] in
private theorem transported_insertions
    {D : Type*} [Category D] [MonoidalCategory D]
    (F : B ⥤ D) [F.OplaxMonoidal] (I : D ⥤ B) (η : 𝟭 B ⟶ F ⋙ I)
    (b : I ⋙ F ≅ 𝟭 D)
    (κ : ∀ X Y : D, F.obj (I.obj X ⊗ I.obj Y) ≅ X ⊗ Y)
    (hc : ∀ X Y : D, (κ X Y).hom = Functor.OplaxMonoidal.δ F (I.obj X) (I.obj Y) ≫
      (b.hom.app X ⊗ₘ b.hom.app Y))
    (hb : ∀ X : B, F.map (η.app X) ≫ b.hom.app (F.obj X) = 𝟙 _) :
    (∀ (X : B) (Y : D), F.map (η.app X ⊗ₘ 𝟙 (I.obj Y)) ≫
      (κ (F.obj X) Y).hom = Functor.OplaxMonoidal.δ F X (I.obj Y) ≫
        (𝟙 _ ⊗ₘ b.hom.app Y)) ∧
    (∀ (X : D) (Y : B), F.map (𝟙 (I.obj X) ⊗ₘ η.app Y) ≫
      (κ X (F.obj Y)).hom = Functor.OplaxMonoidal.δ F (I.obj X) Y ≫
        (b.hom.app X ⊗ₘ 𝟙 _)) := by
  constructor
  · intro X Y
    rw [hc]
    calc
      _ = Functor.OplaxMonoidal.δ F X (I.obj Y) ≫
          (F.map (η.app X) ⊗ₘ F.map (𝟙 (I.obj Y))) ≫
          (b.hom.app (F.obj X) ⊗ₘ b.hom.app Y) :=
        (Functor.OplaxMonoidal.δ_natural_assoc F (η.app X) (𝟙 (I.obj Y)) _).symm
      _ = _ := by
        rw [tensorHom_comp_tensorHom, hb, F.map_id, Category.id_comp]
        rfl
  · intro X Y
    rw [hc]
    calc
      _ = Functor.OplaxMonoidal.δ F (I.obj X) Y ≫
          (F.map (𝟙 (I.obj X)) ⊗ₘ F.map (η.app Y)) ≫
          (b.hom.app X ⊗ₘ b.hom.app (F.obj Y)) :=
        (Functor.OplaxMonoidal.δ_natural_assoc F (𝟙 (I.obj X)) (η.app Y) _).symm
      _ = _ := by
        rw [tensorHom_comp_tensorHom, hb, F.map_id, Category.id_comp]
        rfl

omit [SymmetricCategory B] in
private theorem transported_associator
  {D : Type*} [Category D] [MonoidalCategory D]
  (F : B ⥤ D) [F.Monoidal] (I : D ⥤ B) (η : 𝟭 B ⟶ F ⋙ I)
  (b : I ⋙ F ≅ 𝟭 D)
  (κ : ∀ X Y : D, F.obj (I.obj X ⊗ I.obj Y) ≅ X ⊗ Y)
  (hc : ∀ X Y : D, (κ X Y).hom = Functor.OplaxMonoidal.δ F (I.obj X) (I.obj Y) ≫
    (b.hom.app X ⊗ₘ b.hom.app Y))
  (hil : ∀ (X : B) (Y : D), F.map (η.app X ⊗ₘ 𝟙 (I.obj Y)) ≫
    (κ (F.obj X) Y).hom = Functor.OplaxMonoidal.δ F X (I.obj Y) ≫
      (𝟙 _ ⊗ₘ b.hom.app Y))
  (hir : ∀ (X : D) (Y : B), F.map (𝟙 (I.obj X) ⊗ₘ η.app Y) ≫
    (κ X (F.obj Y)).hom = Functor.OplaxMonoidal.δ F (I.obj X) Y ≫
      (b.hom.app X ⊗ₘ 𝟙 _))
  (hLeft : ∀ X Y : B, IsIso (F.map (η.app X ⊗ₘ 𝟙 Y)))
  (hRight : ∀ X Y : B, IsIso (F.map (𝟙 X ⊗ₘ η.app Y)))
  (X Y Z : D) :
  let (U V : B) := hLeft U V;
  let (U V : B) := hRight U V;
    ((κ (F.obj (I.obj X ⊗ I.obj Y)) Z).hom ≫
      ((κ X Y).hom ⊗ₘ 𝟙 Z) ≫
      (α_ X Y Z).hom ≫
      (𝟙 X ⊗ₘ (κ Y Z).inv) ≫
      (κ X (F.obj (I.obj Y ⊗ I.obj Z))).inv) =
    inv (F.map (η.app ((I.obj X) ⊗ (I.obj Y)) ⊗ₘ 𝟙 (I.obj Z))) ≫
      F.map (α_ (I.obj X) (I.obj Y) (I.obj Z)).hom ≫
      F.map (𝟙 (I.obj X) ⊗ₘ η.app ((I.obj Y) ⊗ (I.obj Z))) := by
  let (U V : B) := hLeft U V
  let (U V : B) := hRight U V
  apply (cancel_epi (F.map (η.app ((I.obj X) ⊗ (I.obj Y)) ⊗ₘ 𝟙 (I.obj Z)))).1
  apply (cancel_mono ((κ X (F.obj (I.obj Y ⊗ I.obj Z))).hom ≫
    (𝟙 X ⊗ₘ (κ Y Z).hom))).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, id_tensorHom,
    whiskerLeft_inv_hom, Category.comp_id,
    IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hil]
  have h1 : (𝟙 (F.obj ((I.obj X) ⊗ (I.obj Y))) ⊗ₘ b.hom.app Z) ≫
      ((κ X Y).hom ⊗ₘ 𝟙 Z) =
      (Functor.OplaxMonoidal.δ F (I.obj X) (I.obj Y) ⊗ₘ 𝟙 (F.obj (I.obj Z))) ≫
        ((b.hom.app X ⊗ₘ b.hom.app Y) ⊗ₘ b.hom.app Z) := by
    simp only [hc, comp_whiskerRight,
      tensorHom_def', whisker_exchange_assoc, id_whiskerRight,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id,
      Functor.comp_obj, Functor.id_obj]
  have hn := associator_naturality (b.hom.app X) (b.hom.app Y) (b.hom.app Z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [Category.assoc, ← Category.assoc _ _
    (α_ X Y Z).hom, h1,
    Category.assoc, hn, ← Category.assoc,
    ← Category.assoc]
  have ha := Functor.OplaxMonoidal.associativity F (I.obj X) (I.obj Y) (I.obj Z)
  simp only [← tensorHom_id, ← id_tensorHom] at ha
  rw [Category.assoc _ _
    (α_ (F.obj (I.obj X)) (F.obj (I.obj Y)) (F.obj (I.obj Z))).hom, ha]
  simp only [Category.assoc]
  have hR := hir X (I.obj Y ⊗ I.obj Z)
  simp only [id_tensorHom] at hR
  congr 1
  rw [← Category.assoc (F.map (I.obj X ◁ η.app (I.obj Y ⊗ I.obj Z)))
    (κ X (F.obj (I.obj Y ⊗ I.obj Z))).hom, hR]
  simp only [hc,
    MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
    ← whisker_exchange_assoc, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id, Functor.id_obj]
  rw [whisker_exchange]

private theorem transported_braiding
    {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]
    (F : B ⥤ D) [F.OplaxMonoidal] (I : D ⥤ B) (b : I ⋙ F ≅ 𝟭 D)
    (κ : ∀ X Y : D, F.obj (I.obj X ⊗ I.obj Y) ≅ X ⊗ Y)
    (hc : ∀ X Y : D, (κ X Y).hom = Functor.OplaxMonoidal.δ F (I.obj X) (I.obj Y) ≫
      (b.hom.app X ⊗ₘ b.hom.app Y))
    (hmap : ∀ U V : B, Functor.OplaxMonoidal.δ F U V ≫
      (β_ (F.obj U) (F.obj V)).hom =
        F.map (β_ U V).hom ≫ Functor.OplaxMonoidal.δ F V U)
    (X Y : D) :
    (κ X Y).hom ≫ (β_ X Y).hom ≫ (κ Y X).inv = F.map (β_ (I.obj X) (I.obj Y)).hom := by
  apply (cancel_mono (κ Y X).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [hc, Category.assoc]
  calc
    _ = Functor.OplaxMonoidal.δ F (I.obj X) (I.obj Y) ≫
        (β_ (F.obj (I.obj X)) (F.obj (I.obj Y))).hom ≫
        (b.hom.app Y ⊗ₘ b.hom.app X) :=
      congrArg (fun k ↦ Functor.OplaxMonoidal.δ F (I.obj X) (I.obj Y) ≫ k)
        (BraidedCategory.braiding_naturality (b.hom.app X) (b.hom.app Y))
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ (b.hom.app Y ⊗ₘ b.hom.app X)) (hmap (I.obj X) (I.obj Y))

/-- A tensor-compatible reflector gives the full local subcategory its normalized
symmetric monoidal structure. Source: Stacks Project, algebraization.tex,
remark-completed-tensor-product (Tag 099G).
(blueprint: lem-pur-reflective-completed-monoidal).

Proof: lift tensor to the full subcategory by applying T, and take T(1) as unit.
The associator is inverse left insertion, T of the original associator, then right
insertion. The braiding is T of the original braiding. Each unitor is inverse
insertion of the unit followed by T of its original unitor and inverse eta on the
local input. Reflection makes T eta invertible. Naturality of eta identifies both
ways of inserting completion into any parenthesized tensor expression. Tensoring
preserves arrows inverted by T: conjugate with the two insertion isomorphisms and
use naturality. Therefore every iterated insertion is invertible. Precompose the
pentagon, triangle and hexagons with their common iterated insertion; they become T
of the original diagrams. Cancel those isomorphisms. Involutivity follows from T
preserving composition and the original symmetry equation. This also proves the
listed formulas, since they were the chosen constraints.

Retain the reflector as a strong symmetric monoidal functor: compose its monoidal
localization with the inverse tensor-transport equivalence. Naturality of the
localization cotensorator and the adjunction triangle identify the new cotensorator
with T(eta_X tensor eta_Y). The transported unit is the identity, and composition
of the braided functors gives its braiding equation. -/
theorem reflectiveCompletedMonoidal
    (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hT : ∀ X : B, P (T.obj X))
    (hbij : ∀ (X Z : B), P Z →
      Function.Bijective (fun f : T.obj X ⟶ Z ↦ η.app X ≫ f))
    (hη : ∀ X : P.FullSubcategory, IsIso (η.app X.obj))
    (hLeft : ∀ X W : B, IsIso (tensorInsertLeft T η X W))
    (hRight : ∀ X W : B, IsIso (tensorInsertRight T η X W)) :
    ∃ (m : MonoidalCategory P.FullSubcategory)
      (s : @SymmetricCategory P.FullSubcategory _ m),
      CompletedConstraintModel P T η hLeft hRight hη m s ∧
      (letI := m
       letI := s
       ∃ mr : (ObjectProperty.lift P T hT).Monoidal,
         letI := mr
         (∀ X Y : B, HEq
           (Functor.OplaxMonoidal.δ (ObjectProperty.lift P T hT) X Y).hom
           (T.map (η.app X ⊗ₘ η.app Y))) ∧
         HEq (Functor.OplaxMonoidal.η (ObjectProperty.lift P T hT)).hom
           (𝟙 (T.obj (𝟙_ B))) ∧
         (∀ X Y : B,
           Functor.OplaxMonoidal.δ (ObjectProperty.lift P T hT) X Y ≫
             (β_ ((ObjectProperty.lift P T hT).obj X)
               ((ObjectProperty.lift P T hT).obj Y)).hom =
           (ObjectProperty.lift P T hT).map (β_ X Y).hom ≫
             Functor.OplaxMonoidal.δ (ObjectProperty.lift P T hT) Y X)) := by
  classical
  let R := reflector P T hT
  let a := reflectorAdjunction P T η hT hbij
  let W := (MorphismProperty.isomorphisms P.FullSubcategory).inverseImage R
  let : W.IsMonoidal := reflector_monoidalEquivalences P T η hT hLeft
  let : R.IsLocalization W := a.isLocalization_leftAdjoint'
  let ε : R.obj (𝟙_ B) ≅ R.obj (𝟙_ B) := Iso.refl _
  let m0 : MonoidalCategory P.FullSubcategory :=
    Localization.Monoidal.instMonoidalCategoryLocalizedMonoidal R W ε
  let s0 : @SymmetricCategory P.FullSubcategory _ m0 :=
    Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal R W ε
  let R' : B ⥤ P.FullSubcategory := Localization.Monoidal.toMonoidalCategory R W ε
  let : R'.Monoidal := instMonoidalLocalizedMonoidalToMonoidalCategory R W ε
  let : R'.Braided :=
    Localization.Monoidal.instBraidedLocalizedMonoidalToMonoidalCategory R W ε
  let incl : P.FullSubcategory ⥤ B := P.ι
  let b : incl ⋙ R' ≅ 𝟭 P.FullSubcategory := by
    change P.ι ⋙ R ≅ 𝟭 P.FullSubcategory
    exact asIso a.counit
  let pre := ((Functor.whiskeringLeft₂ P.FullSubcategory).obj incl).obj incl
  let S : P.FullSubcategory ⥤ P.FullSubcategory ⥤ P.FullSubcategory := {
    obj X := {
      obj Y := R'.obj (X.obj ⊗ Y.obj)
      map g := R'.map (X.obj ◁ g.hom)
      map_id := by
        intro Y
        change R'.map (X.obj ◁ 𝟙 Y.obj) = 𝟙 _
        rw [whiskerLeft_id, R'.map_id]
      map_comp := by
        intro Y Z W f g
        change R'.map (X.obj ◁ (f.hom ≫ g.hom)) = _
        rw [MonoidalCategory.whiskerLeft_comp, R'.map_comp] }
    map f := {
      app Y := R'.map (f.hom ▷ Y.obj)
      naturality := by
        intro Y Z g
        simp only [← R'.map_comp, whisker_exchange] }
    map_id := by
      intro X
      apply NatTrans.ext
      funext Y
      change R'.map (𝟙 X.obj ▷ Y.obj) = 𝟙 _
      rw [id_whiskerRight, R'.map_id]
    map_comp := by
      intro X Y Z f g
      apply NatTrans.ext
      funext W
      change R'.map ((f.hom ≫ g.hom) ▷ W.obj) = _
      rw [comp_whiskerRight, R'.map_comp]
      rfl }
  let c : S ≅ curriedTensor P.FullSubcategory := by
    change pre.obj (curriedTensorPost R') ≅ curriedTensor P.FullSubcategory
    exact pre.mapIso (Functor.curriedTensorPreIsoPost R').symm ≪≫
      curriedTensorPreFunctor.mapIso b
  have hu (X : B) : a.unit.app X = η.app X := by
    change η.app X ≫ 𝟙 (T.obj X) = η.app X
    exact Category.comp_id _
  have hb (X : B) : R'.map (η.app X) ≫ b.hom.app (R'.obj X) = 𝟙 _ := by
    have h := a.left_triangle_components X
    rw [hu] at h
    exact h
  let (X : P.FullSubcategory) : IsIso (η.app X.obj) := hη X
  have hbc (X : P.FullSubcategory) : (b.hom.app X).hom = inv (η.app X.obj) := by
    let := hη X
    apply IsIso.eq_inv_of_hom_inv_id
    have h := a.right_triangle_components X
    rw [hu] at h
    exact h
  have hc (X Y : P.FullSubcategory) :
      ((c.app X).app Y).hom = Functor.OplaxMonoidal.δ R' X.obj Y.obj ≫
        (b.hom.app X ⊗ₘ b.hom.app Y) := rfl
  obtain ⟨hil, hir⟩ :=
    transported_insertions R' incl η b (fun U V ↦ (c.app U).app V) hc hb
  have hηR : Functor.OplaxMonoidal.η R' = 𝟙 (R'.obj (𝟙_ B)) := rfl
  let (X W : B) : IsIso (R'.map (η.app X ⊗ₘ 𝟙 W)) :=
    (ObjectProperty.isIso_hom_iff _).1 (hLeft X W)
  let (X W : B) : IsIso (R'.map (𝟙 X ⊗ₘ η.app W)) :=
    (ObjectProperty.isIso_hom_iff _).1 (hRight X W)
  have ha (X Y Z : P.FullSubcategory) :=
    transported_associator R' incl η b (fun U V ↦ (c.app U).app V) hc hil hir
      (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance) X Y Z
  have hmap (U V : B) :
      Functor.OplaxMonoidal.δ R' U V ≫
        (@BraidedCategory.braiding P.FullSubcategory _ m0 s0.toBraidedCategory
          (R'.obj U) (R'.obj V)).hom =
      R'.map (β_ U V).hom ≫ Functor.OplaxMonoidal.δ R' V U := by
    rw [Functor.map_braiding]
    simp
  have hbr (X Y : P.FullSubcategory) :=
    transported_braiding R' incl b (fun U V ↦ (c.app U).app V) hc hmap X Y
  have hl (X : P.FullSubcategory) : ((c.app (R'.obj (𝟙_ B))).app X).hom ≫
      (@MonoidalCategoryStruct.leftUnitor P.FullSubcategory _ m0.toMonoidalCategoryStruct X).hom =
      inv (R'.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj)) ≫
        R'.map (λ_ X.obj).hom ≫ b.hom.app X := by
    apply (cancel_epi (R'.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj))).1
    simp only [IsIso.hom_inv_id_assoc]
    have HI := congrArg (fun k ↦ k ≫
      (@MonoidalCategoryStruct.leftUnitor P.FullSubcategory _ m0.toMonoidalCategoryStruct X).hom)
      (hil (𝟙_ B) X)
    have H0 := (Category.assoc _ _ _).symm.trans HI
    have H1 := H0.trans (Category.assoc _ _ _)
    have H2 := left_unit_counit R' (b.hom.app X)
    rw [hηR] at H2
    exact H1.trans H2
  have hr (X : P.FullSubcategory) : ((c.app X).app (R'.obj (𝟙_ B))).hom ≫
      (@MonoidalCategoryStruct.rightUnitor P.FullSubcategory _ m0.toMonoidalCategoryStruct X).hom =
      inv (R'.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B))) ≫
        R'.map (ρ_ X.obj).hom ≫ b.hom.app X := by
    apply (cancel_epi (R'.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B)))).1
    simp only [IsIso.hom_inv_id_assoc]
    have HI := congrArg (fun k ↦ k ≫
      (@MonoidalCategoryStruct.rightUnitor P.FullSubcategory _ m0.toMonoidalCategoryStruct X).hom)
      (hir X (𝟙_ B))
    have H0 := (Category.assoc _ _ _).symm.trans HI
    have H1 := H0.trans (Category.assoc _ _ _)
    have H2 := right_unit_counit R' (b.hom.app X)
    rw [hηR] at H2
    exact H1.trans H2
  have hs0 (X Y : P.FullSubcategory) :
      (((c.app X).app Y) ≪≫ (β_ X Y) ≪≫ ((c.app Y).app X).symm).hom ≫
      (((c.app Y).app X) ≪≫ (β_ Y X) ≪≫ ((c.app X).app Y).symm).hom = 𝟙 _ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      SymmetricCategory.symmetry_assoc, Iso.hom_inv_id]
  let : Category (Sheaf.Retensor.Copy P.FullSubcategory) :=
    inferInstanceAs (Category P.FullSubcategory)
  let m : MonoidalCategory (Sheaf.Retensor.Copy P.FullSubcategory) :=
    @Sheaf.Retensor.monoidal P.FullSubcategory _ m0 S c
  let br : @BraidedCategory (Sheaf.Retensor.Copy P.FullSubcategory) _ m :=
    @Sheaf.Retensor.braided P.FullSubcategory _ m0 S c s0.toBraidedCategory
  let s : @SymmetricCategory (Sheaf.Retensor.Copy P.FullSubcategory) _ m := by
    let := m
    let := br
    refine { toBraidedCategory := br, symmetry := fun X Y ↦ ?_ }
    dsimp +instances only [br, Sheaf.Retensor.braided, BraidedCategory.ofFaithful]
    exact hs0 X Y
  refine ⟨m, s, ?_, ?_⟩
  swap
  · let := m
    let := s
    let I : P.FullSubcategory ⥤ Sheaf.Retensor.Copy P.FullSubcategory :=
      Sheaf.Retensor.equivalence.inverse
    let : I.Monoidal := Sheaf.Retensor.inverseMonoidal S c
    let : I.Braided := Sheaf.Retensor.inverseBraided S c
    let Rn : B ⥤ Sheaf.Retensor.Copy P.FullSubcategory := R' ⋙ I
    let rn : Rn.Monoidal := inferInstance
    refine ⟨rn, ?_, ?_, ?_⟩
    · intro X Y
      apply heq_of_eq
      change (Functor.OplaxMonoidal.δ R' X Y ≫
        Functor.OplaxMonoidal.δ I (R'.obj X) (R'.obj Y)).hom = _
      rw [Sheaf.Retensor.inverse_δ]
      have hn := Functor.OplaxMonoidal.δ_natural R' (η.app X) (η.app Y)
      have hh := congrArg (fun f ↦ f ≫
        (b.hom.app (R'.obj X) ⊗ₘ b.hom.app (R'.obj Y))) hn
      simp only [Category.assoc, tensorHom_comp_tensorHom, hb,
        tensorHom_id, id_whiskerRight, Category.comp_id] at hh
      have hins : R'.map (η.app X ⊗ₘ η.app Y) ≫
          ((c.app (R'.obj X)).app (R'.obj Y)).hom =
          Functor.OplaxMonoidal.δ R' X Y := hh.symm
      have hδ : Functor.OplaxMonoidal.δ R' X Y ≫
          ((c.app (R'.obj X)).app (R'.obj Y)).inv =
          R'.map (η.app X ⊗ₘ η.app Y) := by
        rw [← hins]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact congrArg (fun f ↦ incl.map f) hδ
    · apply heq_of_eq
      change (Functor.OplaxMonoidal.η R' ≫ Functor.OplaxMonoidal.η I).hom = _
      have hi := @Sheaf.Retensor.inverse_ε P.FullSubcategory _ m0 S c
      have hi' : Functor.OplaxMonoidal.η I = 𝟙 _ := by
        apply (cancel_epi (Functor.LaxMonoidal.ε I)).1
        simp only [Functor.Monoidal.ε_η, Category.comp_id]
        convert hi.symm using 1 <;> rfl
      rw [hηR, hi', Category.id_comp]
      rfl
    · intro X Y
      have hn : Functor.OplaxMonoidal.δ Rn X Y ≫
          (β_ (Rn.obj X) (Rn.obj Y)).hom =
          Rn.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ Rn Y X := by
        let : Rn.Braided := inferInstance
        rw [Functor.map_braiding]
        simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
      exact hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y
    rfl
  · intro X Y X' Y' f g
    apply heq_of_eq
    dsimp +instances only [m, Sheaf.Retensor.monoidal, Monoidal.induced,
      Sheaf.Retensor.struct, S, pre, curriedTensorPost,
      Functor.whiskeringLeft₂, incl, R',
      Localization.Monoidal.toMonoidalCategory, R, reflector, ObjectProperty.lift]
    try dsimp only [Functor.comp_obj, Functor.comp_map, Functor.whiskeringLeft_obj_obj,
      Functor.whiskeringLeft_obj_map, Functor.whiskeringRight_obj_obj,
      Functor.whiskeringRight_obj_map, Functor.postcompose₂, ObjectProperty.ι,
      curriedTensor, Functor.whiskerRight, Functor.whiskerLeft]
    change T.map (f.hom ▷ Y.obj) ≫ T.map (X'.obj ◁ g.hom) = _
    simp only [← tensorHom_id, ← id_tensorHom]
    rw [← T.map_comp, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  · rfl
  · intro X Y Z
    apply heq_of_eq
    dsimp +instances only [m, Sheaf.Retensor.monoidal, Monoidal.induced,
      Sheaf.Retensor.struct]
    have h := congrArg (fun f ↦ incl.map f) (ha X Y Z)
    simpa +instances only [Sheaf.Retensor.cmp, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, Iso.symm_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.hom_inv, ObjectProperty.lift,
      ObjectProperty.homMk, S, pre, curriedTensorPost, tensorInsertLeft,
      tensorInsertRight, R',
      Localization.Monoidal.toMonoidalCategory, R, reflector, incl, ObjectProperty.ι,
      inducedFunctor,
      Functor.map_comp, Functor.map_inv] using h
  · intro X Y
    apply heq_of_eq
    dsimp +instances only [s, br, Sheaf.Retensor.braided, BraidedCategory.ofFaithful]
    exact congrArg (fun f ↦ incl.map f) (hbr X Y)
  · intro X
    apply heq_of_eq
    dsimp +instances only [m, Sheaf.Retensor.monoidal, Monoidal.induced,
      Sheaf.Retensor.struct]
    have h := congrArg (fun f ↦ incl.map f) (hl (show P.FullSubcategory from X))
    change ((c.app (R'.obj (𝟙_ B))).app X).hom.hom ≫
      (@MonoidalCategoryStruct.leftUnitor P.FullSubcategory _
        m0.toMonoidalCategoryStruct X).hom.hom =
      (inv (R'.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj))).hom ≫
        (R'.map (λ_ X.obj).hom).hom ≫ (b.hom.app X).hom at h
    let : IsIso (T.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj)) := hLeft _ _
    let : IsIso (R'.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj)) :=
      (ObjectProperty.isIso_hom_iff _).1 (hLeft _ _)
    have hi : (inv (R'.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj))).hom =
        inv (T.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj)) := by
      exact incl.map_inv (R'.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj))
    have H := congrArg (fun k ↦ inv (T.map (η.app (𝟙_ B) ⊗ₘ 𝟙 X.obj)) ≫
      T.map (λ_ X.obj).hom ≫ k) (hbc (show P.FullSubcategory from X))
    rw [hi] at h
    exact h.trans H
  · intro X
    apply heq_of_eq
    dsimp +instances only [m, Sheaf.Retensor.monoidal, Monoidal.induced,
      Sheaf.Retensor.struct]
    have h := congrArg (fun f ↦ incl.map f) (hr (show P.FullSubcategory from X))
    change ((c.app X).app (R'.obj (𝟙_ B))).hom.hom ≫
      (@MonoidalCategoryStruct.rightUnitor P.FullSubcategory _
        m0.toMonoidalCategoryStruct X).hom.hom =
      (inv (R'.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B)))).hom ≫
        (R'.map (ρ_ X.obj).hom).hom ≫ (b.hom.app X).hom at h
    let : IsIso (T.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B))) := hRight _ _
    let : IsIso (R'.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B))) :=
      (ObjectProperty.isIso_hom_iff _).1 (hRight _ _)
    have hi : (inv (R'.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B)))).hom =
        inv (T.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B))) := by
      exact incl.map_inv (R'.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B)))
    have H := congrArg (fun k ↦ inv (T.map (𝟙 X.obj ⊗ₘ η.app (𝟙_ B))) ≫
      T.map (ρ_ X.obj).hom ≫ k) (hbc (show P.FullSubcategory from X))
    rw [hi] at h
    exact h.trans H

end CategoryTheory.ConstantCompletion
