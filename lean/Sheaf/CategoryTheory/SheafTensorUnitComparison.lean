/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.SheafificationTensorLocalIso

/-! # Sheaf tensor unit comparison identities

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md, second paragraph,
first sentence (blueprint: lem-sfb-sheaf-tensor-unit-comparison).
-/

@[expose] public section

universe uC vC uA vA w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- The sheaf tensor before coherence, given by sheafification of the objectwise tensor.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafTensor
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (F G : Sheaf J A) : Sheaf J A :=
  (presheafToSheaf J A).obj (F.obj ⊗ G.obj)

/-- The tensor of sheaf morphisms, defined by sheafifying their objectwise tensor.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafTensorMap
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G') :
    sfbSheafTensor J F G ⟶ sfbSheafTensor J F' G' :=
  (presheafToSheaf J A).map (f.hom ⊗ₘ g.hom)

/-- The sheafification counit on a sheaf, inverse to the unit at its underlying presheaf.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafEpsilon
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (F : Sheaf J A) :
    (presheafToSheaf J A).obj F.obj ⟶ F :=
  (sheafificationAdjunction J A).counit.app F

/-- The comparison d(f,g), tensoring the arbitrary leaf maps and then applying the unit.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafD
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] {P Q : Cᵒᵖ ⥤ A} {F G : Sheaf J A}
    (f : P ⟶ F.obj) (g : Q ⟶ G.obj) :
    P ⊗ Q ⟶ (sfbSheafTensor J F G).obj :=
  (f ⊗ₘ g) ≫ toSheafify J (F.obj ⊗ G.obj)


/-- The sheafification of a unit tensored on the left, regarded as an isomorphism.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafTensorUnitLeftIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (X Y : Cᵒᵖ ⥤ A) :
    (presheafToSheaf J A).obj (X ⊗ Y) ≅
      (presheafToSheaf J A).obj (sheafify J X ⊗ Y) := by
  letI : IsIso ((presheafToSheaf J A).map (toSheafify J X ⊗ₘ 𝟙 Y)) := by
    apply (J.W_iff _).mp
    exact (sheafification_tensor_local_iso J).2.1 (toSheafify J X) Y (J.W_toSheafify X) |>.2
  exact asIso ((presheafToSheaf J A).map (toSheafify J X ⊗ₘ 𝟙 Y))

/-- The sheafification of a unit tensored on the right, regarded as an isomorphism.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafTensorUnitRightIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (X Y : Cᵒᵖ ⥤ A) :
    (presheafToSheaf J A).obj (X ⊗ Y) ≅
      (presheafToSheaf J A).obj (X ⊗ sheafify J Y) := by
  letI : IsIso ((presheafToSheaf J A).map (𝟙 X ⊗ₘ toSheafify J Y)) := by
    apply (J.W_iff _).mp
    exact (sheafification_tensor_local_iso J).2.1 (toSheafify J Y) X (J.W_toSheafify Y) |>.1
  exact asIso ((presheafToSheaf J A).map (𝟙 X ⊗ₘ toSheafify J Y))

/-- The associator map, defined before coherence by the displayed inverse comparisons.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafAssociator
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (F G H : Sheaf J A) :
    sfbSheafTensor J (sfbSheafTensor J F G) H ⟶
      sfbSheafTensor J F (sfbSheafTensor J G H) := by
  exact (sfbSheafTensorUnitLeftIso J (F.obj ⊗ G.obj) H.obj).inv ≫
      (presheafToSheaf J A).map (α_ F.obj G.obj H.obj).hom ≫
      (sfbSheafTensorUnitRightIso J F.obj (G.obj ⊗ H.obj)).hom

/-- The left unitor map, defined before coherence using the unit comparison and counit.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafLeftUnitor
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (F : Sheaf J A) :
    sfbSheafTensor J ((presheafToSheaf J A).obj ((Functor.const Cᵒᵖ).obj (𝟙_ A))) F ⟶ F := by
  exact (sfbSheafTensorUnitLeftIso J ((Functor.const Cᵒᵖ).obj (𝟙_ A)) F.obj).inv ≫
    (presheafToSheaf J A).map (λ_ F.obj).hom ≫ sfbSheafEpsilon J F

/-- The right unitor map, defined before coherence using the unit comparison and counit.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafRightUnitor
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (F : Sheaf J A) :
    sfbSheafTensor J F ((presheafToSheaf J A).obj ((Functor.const Cᵒᵖ).obj (𝟙_ A))) ⟶ F := by
  exact (sfbSheafTensorUnitRightIso J F.obj ((Functor.const Cᵒᵖ).obj (𝟙_ A))).inv ≫
    (presheafToSheaf J A).map (ρ_ F.obj).hom ≫ sfbSheafEpsilon J F

/-- The braiding map, defined before coherence by sheafifying the presheaf symmetry.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
first two paragraphs (blueprint: lem-sfb-sheaf-tensor-unit-comparison). -/
noncomputable def sfbSheafBraiding
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] (F G : Sheaf J A) :
    sfbSheafTensor J F G ⟶ sfbSheafTensor J G F :=
  (presheafToSheaf J A).map (β_ F.obj G.obj).hom

/-- The four comparison identities: the explicit sheaf associator, unitors and braiding,
taken before any coherence, commute with the unit comparisons `d(f,g)` for arbitrary leaf
maps `f`, `g`, `h` into sheaves.
Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-structure.proof.md`,
second paragraph, first sentence (blueprint: lem-sfb-sheaf-tensor-unit-comparison).

Proof:
(1) For a presheaf `X`, precomposition with `η_X` is a bijection onto maps into sheaves, so
`η_X ∈ J.W`; clause 1 of `sheafification_tensor_local_iso` makes `a(η_X ⊗ 𝟙 Y)` and
`a(𝟙 Y ⊗ η_X)` invertible, which are all the inverses used. The counit on a sheaf `T`
satisfies `η_(iT) ≫ i(ε_T) = 𝟙` by the triangle identity and uniqueness of extensions.
(2) Unit naturality: `η_X ≫ ia(t) = t ≫ η_Y`; when `a(t)` is invertible,
`t ≫ η_Y ≫ i(a(t)⁻¹) = η_X`.
(3) Associator: with `t = η_(iF ⊗ iG) ⊗ 𝟙` and `k = (f ⊗ g) ⊗ h`, tensor bifunctoriality
gives `d(d(f,g),h) = k ≫ t ≫ η`; cancel `a(t)⁻¹` by (2), apply unit naturality to
`α_ ≫ (𝟙 ⊗ η_(iG ⊗ iH))`, then naturality of the presheaf associator.
(4) Left unitor: `d(η_I,f) = (𝟙 ⊗ f) ≫ (η_I ⊗ 𝟙) ≫ η`; cancel by (2), use unit naturality
for `λ_ (iF)`, `η_(iF) ≫ i(ε_F) = 𝟙` from (1), then presheaf left unitor naturality.
(5) Right unitor: the same with `f ⊗ 𝟙`, `𝟙 ⊗ η_I` and presheaf right unitor naturality.
(6) Braiding: unit naturality for `β_ (iF) (iG)` and presheaf braiding naturality.
No coherence, naturality or monoidality of the displayed sheaf maps is assumed.
-/
theorem sfbSheafTensorUnitComparison
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A]
    {P Q R : Cᵒᵖ ⥤ A} {F G H : Sheaf J A}
    (f : P ⟶ F.obj) (g : Q ⟶ G.obj) (h : R ⟶ H.obj) :
    (sfbSheafD J (sfbSheafD J f g) h) ≫
          (sfbSheafAssociator J F G H).hom =
        (α_ P Q R).hom ≫ sfbSheafD J f (sfbSheafD J g h) ∧
      (sfbSheafD J (toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A))) f) ≫
          (sfbSheafLeftUnitor J F).hom =
        (λ_ P).hom ≫ f ∧
      (sfbSheafD J f (toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A)))) ≫
          (sfbSheafRightUnitor J F).hom =
        (ρ_ P).hom ≫ f ∧
      (sfbSheafD J f g) ≫ (sfbSheafBraiding J F G).hom =
        (β_ P Q).hom ≫ sfbSheafD J g f := by
  have cancelUnit {X Y : Cᵒᵖ ⥤ A} (t : X ⟶ Y)
      (e : (presheafToSheaf J A).obj X ≅ (presheafToSheaf J A).obj Y)
      (he : e.hom = (presheafToSheaf J A).map t) :
      t ≫ toSheafify J Y ≫ e.inv.hom = toSheafify J X := by
    rw [toSheafify_naturality_assoc]
    change toSheafify J X ≫ ((presheafToSheaf J A).map t).hom ≫ e.inv.hom = _
    rw [← he]
    change toSheafify J X ≫ (sheafToPresheaf J A).map e.hom ≫
      (sheafToPresheaf J A).map e.inv = _
    rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
    exact Category.comp_id _
  have cancelLeft (X Y : Cᵒᵖ ⥤ A) :
      (toSheafify J X ⊗ₘ 𝟙 Y) ≫ toSheafify J (sheafify J X ⊗ Y) ≫
        (sfbSheafTensorUnitLeftIso J X Y).inv.hom = toSheafify J (X ⊗ Y) :=
    cancelUnit _ _ rfl
  have cancelRight (X Y : Cᵒᵖ ⥤ A) :
      (𝟙 X ⊗ₘ toSheafify J Y) ≫ toSheafify J (X ⊗ sheafify J Y) ≫
        (sfbSheafTensorUnitRightIso J X Y).inv.hom = toSheafify J (X ⊗ Y) :=
    cancelUnit _ _ rfl
  have counitUnit (T : Sheaf J A) :
      toSheafify J T.obj ≫ (sfbSheafEpsilon J T).hom = 𝟙 T.obj :=
    (sheafificationAdjunction J A).right_triangle_components T
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ht : ((f ⊗ₘ g) ≫ toSheafify J (F.obj ⊗ G.obj)) ⊗ₘ h =
        ((f ⊗ₘ g) ⊗ₘ h) ≫ (toSheafify J (F.obj ⊗ G.obj) ⊗ₘ 𝟙 H.obj) := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id]
    dsimp only [sfbSheafD, sfbSheafAssociator, sfbSheafTensor]
    rw [ht]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    rw [reassoc_of% (cancelLeft (F.obj ⊗ G.obj) H.obj)]
    change ((f ⊗ₘ g) ⊗ₘ h) ≫ toSheafify J _ ≫
      sheafifyMap J (α_ F.obj G.obj H.obj).hom ≫
      sheafifyMap J (𝟙 F.obj ⊗ₘ toSheafify J (G.obj ⊗ H.obj)) = _
    rw [← toSheafify_naturality_assoc, ← toSheafify_naturality]
    rw [← Category.assoc, associator_naturality, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id]
  · have ht : toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A)) ⊗ₘ f =
        (𝟙 ((Functor.const Cᵒᵖ).obj (𝟙_ A)) ⊗ₘ f) ≫
          (toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A)) ⊗ₘ 𝟙 F.obj) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    dsimp only [sfbSheafD, sfbSheafLeftUnitor]
    rw [ht]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    rw [reassoc_of% (cancelLeft ((Functor.const Cᵒᵖ).obj (𝟙_ A)) F.obj)]
    change (𝟙 _ ⊗ₘ f) ≫ toSheafify J _ ≫
      sheafifyMap J (λ_ F.obj).hom ≫ (sfbSheafEpsilon J F).hom = _
    rw [← toSheafify_naturality_assoc, counitUnit, Category.comp_id]
    simpa only [id_tensorHom] using leftUnitor_naturality f
  · have ht : f ⊗ₘ toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A)) =
        (f ⊗ₘ 𝟙 ((Functor.const Cᵒᵖ).obj (𝟙_ A))) ≫
          (𝟙 F.obj ⊗ₘ toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A))) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    dsimp only [sfbSheafD, sfbSheafRightUnitor]
    rw [ht]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    rw [reassoc_of% (cancelRight F.obj ((Functor.const Cᵒᵖ).obj (𝟙_ A)))]
    change (f ⊗ₘ 𝟙 _) ≫ toSheafify J _ ≫
      sheafifyMap J (ρ_ F.obj).hom ≫ (sfbSheafEpsilon J F).hom = _
    rw [← toSheafify_naturality_assoc, counitUnit, Category.comp_id]
    simpa only [tensorHom_id] using rightUnitor_naturality f
  · change ((f ⊗ₘ g) ≫ toSheafify J (F.obj ⊗ G.obj)) ≫
      sheafifyMap J (β_ F.obj G.obj).hom =
        (β_ P Q).hom ≫ (g ⊗ₘ f) ≫ toSheafify J (G.obj ⊗ F.obj)
    rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc,
      BraidedCategory.braiding_naturality, Category.assoc]

end CategoryTheory
