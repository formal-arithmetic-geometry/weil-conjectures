/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# The adjunction induced on complexes, on the homotopy category, and on its bounded part

An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes (`CategoryTheory.Adjunction.mapHomologicalComplex`),
with unit and counit given degreewise by the unit and counit of `adj`.

Since `HomotopyCategory.quotient` is a localization functor for the homotopy equivalences,
that adjunction descends to the homotopy categories
(`CategoryTheory.Adjunction.mapHomotopyCategory`), and restricting along the fully faithful
inclusions of the bounded below subcategories gives an adjunction between the bounded below
homotopy categories (`CategoryTheory.Adjunction.mapHomotopyCategoryPlus`).

We also record how these adjunctions behave under identities and composition: the unit of
the adjunction induced by `Adjunction.id` is the inverse of the isomorphism
`Functor.mapHomotopyCategoryPlusIdIso`, and the unit of the adjunction induced by a
composite `adj₁.comp adj₂` is the composite of the two units, transported along
`Functor.mapHomotopyCategoryPlusCompIso`. Both are proved by descending to categories of
complexes, where the unit is given degreewise by the unit of `adj`.

## Main definitions

- `CategoryTheory.Adjunction.mapHomologicalComplex`
- `CategoryTheory.Adjunction.mapHomotopyCategory`
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus`

## Main results

- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_id_unit_app`: the identity law.
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_comp_unit_app`: the composition law.
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_unit_app_comp`: if an adjunction
  `L ⊣ R` of endofunctors comes with isomorphisms `L ≅ 𝟭` and `R ≅ 𝟭` that correspond to
  each other under the conjugation bijection, in the form of the unit relation
  `adj.unit ≫ R(u) = l⁻¹`, then the same relation holds for the induced adjunction on the
  bounded below homotopy categories.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {ι : Type*} (c : ComplexShape ι)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes. -/
noncomputable def Adjunction.mapHomologicalComplex {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c where
  unit :=
    { app := fun M =>
        { f := fun n => adj.unit.app (M.X n)
          comm' := fun i j _ => (adj.unit.naturality (M.d i j)).symm }
      naturality := fun M N φ => by
        ext n
        exact adj.unit.naturality (φ.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => adj.counit.app (K.X n)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L ψ => by
        ext n
        exact adj.counit.naturality (ψ.f n) }
  left_triangle_components X := by
    ext n
    exact adj.left_triangle_components (X.X n)
  right_triangle_components Y := by
    ext n
    exact adj.right_triangle_components (Y.X n)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c` between the induced functors on the
homotopy categories: both induced functors factor the corresponding functors on complexes
through the quotient functors, which are localization functors for the homotopy
equivalences, so `Adjunction.mapHomologicalComplex` descends. -/
noncomputable def Adjunction.mapHomotopyCategory {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive]
    [(HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences C c)]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)] :
    G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c := by
  letI : CatCommSq (G.mapHomologicalComplex c) (HomotopyCategory.quotient D c)
      (HomotopyCategory.quotient C c) (G.mapHomotopyCategory c) :=
    ⟨(G.mapHomotopyCategoryFactors c).symm⟩
  letI : CatCommSq (F.mapHomologicalComplex c) (HomotopyCategory.quotient C c)
      (HomotopyCategory.quotient D c) (F.mapHomotopyCategory c) :=
    ⟨(F.mapHomotopyCategoryFactors c).symm⟩
  exact (adj.mapHomologicalComplex c).localization
    (HomotopyCategory.quotient D c) (HomologicalComplex.homotopyEquivalences D c)
    (HomotopyCategory.quotient C c) (HomologicalComplex.homotopyEquivalences C c)
    (G.mapHomotopyCategory c) (F.mapHomotopyCategory c)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus` between the bounded below homotopy
categories: both functors are restrictions of the corresponding functors on the ambient
homotopy categories along the fully faithful inclusions of the bounded below
subcategories. -/
noncomputable def Adjunction.mapHomotopyCategoryPlus [Limits.HasBinaryBiproducts C]
    [Limits.HasBinaryBiproducts D] {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus :=
  Adjunction.restrictFullyFaithful (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.plus D).fullyFaithfulι (HomotopyCategory.plus C).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

namespace Adjunction

section MapHomologicalComplex

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [R.Additive]

@[simp]
lemma mapHomologicalComplex_unit_app_f (X : HomologicalComplex C c) (n : ι) :
    ((adj.mapHomologicalComplex c).unit.app X).f n = adj.unit.app (X.X n) := rfl

@[simp]
lemma mapHomologicalComplex_counit_app_f (Y : HomologicalComplex D c) (n : ι) :
    ((adj.mapHomologicalComplex c).counit.app Y).f n = adj.counit.app (Y.X n) := rfl

end MapHomologicalComplex

/-- The identity law for `Adjunction.mapHomologicalComplex`: the unit of the adjunction
induced by `Adjunction.id` is the inverse of `Functor.mapHomologicalComplexIdIso`. -/
lemma mapHomologicalComplex_id_unit_app (X : HomologicalComplex C c) :
    ((Adjunction.id (C := C)).mapHomologicalComplex c).unit.app X =
      (Functor.mapHomologicalComplexIdIso C c).inv.app X ≫
        ((𝟭 C).mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexIdIso C c).inv.app X) := by
  ext n
  simp

variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- The composition law for `Adjunction.mapHomologicalComplex`: the unit of the adjunction
induced by a composite of adjunctions is the composite of the two units, transported along
`Functor.mapHomologicalComplexCompIso`. -/
lemma mapHomologicalComplex_comp_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    (X : HomologicalComplex C c) :
    ((adj₁.comp adj₂).mapHomologicalComplex c).unit.app X =
      (adj₁.mapHomologicalComplex c).unit.app X ≫
        (R₁.mapHomologicalComplex c).map ((adj₂.mapHomologicalComplex c).unit.app
          ((L₁.mapHomologicalComplex c).obj X)) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
          ((L₂.mapHomologicalComplex c).obj ((L₁.mapHomologicalComplex c).obj X)) ≫
        ((R₂ ⋙ R₁).mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app X) := by
  have e₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app X = 𝟙 _ := rfl
  have e₂ : ∀ Z, (Functor.mapHomologicalComplexCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app Z =
      𝟙 _ := fun _ => rfl
  rw [e₁, e₂]
  ext n
  simp only [Functor.id_obj, Functor.comp_obj, mapHomologicalComplex_unit_app_f, comp_unit_app,
    Functor.map_id, Category.comp_id, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  rfl

section Localization

variable [(HomotopyCategory.quotient C c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C c)]

/-- The unit of `Adjunction.mapHomotopyCategory` on the image of a complex is the image of
the unit of `Adjunction.mapHomologicalComplex`. -/
lemma mapHomotopyCategory_unit_app_quotient {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [R.Additive]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)]
    (X : HomologicalComplex C c) :
    (adj.mapHomotopyCategory c).unit.app ((HomotopyCategory.quotient C c).obj X) =
      (HomotopyCategory.quotient C c).map ((adj.mapHomologicalComplex c).unit.app X) := by
  have key : (R.mapHomotopyCategoryFactors c).inv.app ((L.mapHomologicalComplex c).obj X) ≫
      (R.mapHomotopyCategory c).map ((L.mapHomotopyCategoryFactors c).inv.app X) =
      𝟙 ((R.mapHomotopyCategory c).obj
        ((L.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj X))) := by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Functor.comp_obj]
    rw [(R.mapHomotopyCategory c).map_id]
    apply Category.comp_id
  rw [Adjunction.mapHomotopyCategory, Adjunction.localization_unit_app]
  exact (congrArg (fun t => (HomotopyCategory.quotient C c).map
      ((adj.mapHomologicalComplex c).unit.app X) ≫ t) key).trans (Category.comp_id _)

/-- The identity law for `Adjunction.mapHomotopyCategory`. -/
lemma mapHomotopyCategory_id_unit_app (Y : HomotopyCategory C c) :
    ((Adjunction.id (C := C)).mapHomotopyCategory c).unit.app Y =
      (Functor.mapHomotopyCategoryIdIso C c).inv.app Y ≫
        ((𝟭 C).mapHomotopyCategory c).map ((Functor.mapHomotopyCategoryIdIso C c).inv.app Y) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hmap : ∀ {A B : HomologicalComplex C c} (f : A ⟶ B),
      ((𝟭 C).mapHomotopyCategory c).map ((HomotopyCategory.quotient C c).map f) =
        (HomotopyCategory.quotient C c).map (((𝟭 C).mapHomologicalComplex c).map f) :=
    fun _ => rfl
  rw [mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategoryIdIso_inv_app, hmap,
    ← Functor.map_comp, ← mapHomologicalComplex_id_unit_app]

/-- The composition law for `Adjunction.mapHomotopyCategory`. -/
lemma mapHomotopyCategory_comp_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)]
    [(HomotopyCategory.quotient E c).IsLocalization
      (HomologicalComplex.homotopyEquivalences E c)]
    (Y : HomotopyCategory C c) :
    ((adj₁.comp adj₂).mapHomotopyCategory c).unit.app Y =
      (adj₁.mapHomotopyCategory c).unit.app Y ≫
        (R₁.mapHomotopyCategory c).map ((adj₂.mapHomotopyCategory c).unit.app
          ((L₁.mapHomotopyCategory c).obj Y)) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
          ((L₂.mapHomotopyCategory c).obj ((L₁.mapHomotopyCategory c).obj Y)) ≫
        ((R₂ ⋙ R₁).mapHomotopyCategory c).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app Y) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hmapR₁ : ∀ {A B : HomologicalComplex D c} (f : A ⟶ B),
      (R₁.mapHomotopyCategory c).map ((HomotopyCategory.quotient D c).map f) =
        (HomotopyCategory.quotient C c).map ((R₁.mapHomologicalComplex c).map f) := fun _ => rfl
  have hmapR : ∀ {A B : HomologicalComplex E c} (f : A ⟶ B),
      ((R₂ ⋙ R₁).mapHomotopyCategory c).map ((HomotopyCategory.quotient E c).map f) =
        (HomotopyCategory.quotient C c).map (((R₂ ⋙ R₁).mapHomologicalComplex c).map f) :=
    fun _ => rfl
  have h₂ : (adj₂.mapHomotopyCategory c).unit.app
      ((L₁.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj X)) =
      (HomotopyCategory.quotient D c).map ((adj₂.mapHomologicalComplex c).unit.app
        ((L₁.mapHomologicalComplex c).obj X)) :=
    mapHomotopyCategory_unit_app_quotient c adj₂ _
  have hciL : (Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app
      ((HomotopyCategory.quotient C c).obj X) =
      (HomotopyCategory.quotient E c).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app X) := rfl
  have hciR : (Functor.mapHomotopyCategoryCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
      ((L₂.mapHomotopyCategory c).obj
        ((L₁.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj X))) =
      (HomotopyCategory.quotient C c).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
          ((L₂.mapHomologicalComplex c).obj ((L₁.mapHomologicalComplex c).obj X))) := rfl
  rw [mapHomotopyCategory_unit_app_quotient, mapHomotopyCategory_unit_app_quotient,
    h₂, hmapR₁, hciR, hciL, hmapR, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← mapHomologicalComplex_comp_unit_app]

end Localization

section Plus

variable [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts D]
  [Limits.HasBinaryBiproducts E]

/-- The unit of `Adjunction.mapHomotopyCategoryPlus` is the restriction of the unit of
`Adjunction.mapHomotopyCategory` along the inclusion of the bounded below subcategory. -/
@[simp]
lemma ι_map_mapHomotopyCategoryPlus_unit_app {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [R.Additive] (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι C).map (adj.mapHomotopyCategoryPlus.unit.app K) =
      (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K.obj := by
  rw [Adjunction.mapHomotopyCategoryPlus, Adjunction.map_restrictFullyFaithful_unit_app]
  simp

/-- **The identity law for `Adjunction.mapHomotopyCategoryPlus`**: the unit of the
adjunction induced by `Adjunction.id` is the inverse of
`Functor.mapHomotopyCategoryPlusIdIso`. -/
lemma mapHomotopyCategoryPlus_id_unit_app (K : HomotopyCategory.Plus C) :
    (Adjunction.id (C := C)).mapHomotopyCategoryPlus.unit.app K =
      (Functor.mapHomotopyCategoryPlusIdIso C).inv.app K ≫
        (𝟭 C).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusIdIso C).inv.app K) := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmap : ∀ {A B : HomotopyCategory.Plus C} (f : A ⟶ B),
      (HomotopyCategory.Plus.ι C).map ((𝟭 C).mapHomotopyCategoryPlus.map f) =
        ((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι C).map f) := fun _ => rfl
  rw [ι_map_mapHomotopyCategoryPlus_unit_app, Functor.map_comp, hmap,
    Functor.ι_map_mapHomotopyCategoryPlusIdIso_inv_app,
    mapHomotopyCategory_id_unit_app]

/-- **The composition law for `Adjunction.mapHomotopyCategoryPlus`**: the unit of the
adjunction induced by a composite of adjunctions is the composite of the two units,
transported along `Functor.mapHomotopyCategoryPlusCompIso`. -/
lemma mapHomotopyCategoryPlus_comp_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] (K : HomotopyCategory.Plus C) :
    (adj₁.comp adj₂).mapHomotopyCategoryPlus.unit.app K =
      adj₁.mapHomotopyCategoryPlus.unit.app K ≫
        R₁.mapHomotopyCategoryPlus.map (adj₂.mapHomotopyCategoryPlus.unit.app
          (L₁.mapHomotopyCategoryPlus.obj K)) ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (R₂ ⋙ R₁))).hom.app
          (L₂.mapHomotopyCategoryPlus.obj (L₁.mapHomotopyCategoryPlus.obj K)) ≫
        (R₂ ⋙ R₁).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K) := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmapR₁ : ∀ {A B : HomotopyCategory.Plus D} (f : A ⟶ B),
      (HomotopyCategory.Plus.ι C).map (R₁.mapHomotopyCategoryPlus.map f) =
        (R₁.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι D).map f) := fun _ => rfl
  have hmapR : ∀ {A B : HomotopyCategory.Plus E} (f : A ⟶ B),
      (HomotopyCategory.Plus.ι C).map ((R₂ ⋙ R₁).mapHomotopyCategoryPlus.map f) =
        ((R₂ ⋙ R₁).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι E).map f) := fun _ => rfl
  have hciL : (HomotopyCategory.Plus.ι E).map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) (ComplexShape.up ℤ)).hom.app
        K.obj := rfl
  have hciR : (HomotopyCategory.Plus.ι C).map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (R₂ ⋙ R₁))).hom.app
        (L₂.mapHomotopyCategoryPlus.obj (L₁.mapHomotopyCategoryPlus.obj K))) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R₂ ⋙ R₁)) (ComplexShape.up ℤ)).hom.app
        ((L₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((L₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj)) := rfl
  have h₂ : (HomotopyCategory.Plus.ι D).map (adj₂.mapHomotopyCategoryPlus.unit.app
      (L₁.mapHomotopyCategoryPlus.obj K)) =
      (adj₂.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((L₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) :=
    ι_map_mapHomotopyCategoryPlus_unit_app adj₂ _
  rw [ι_map_mapHomotopyCategoryPlus_unit_app, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, ι_map_mapHomotopyCategoryPlus_unit_app, hmapR₁, h₂, hciR, hmapR, hciL,
    mapHomotopyCategory_comp_unit_app]

end Plus

section Conjugate

variable {L R : C ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R) (u : L ≅ 𝟭 C) (l : R ≅ 𝟭 C)
  (h : ∀ X, adj.unit.app X ≫ R.map (u.hom.app X) = l.inv.app X)

include h in
/-- Transport to complexes of the unit relation `adj.unit ≫ R(u) = l⁻¹` between an
adjunction `L ⊣ R` of endofunctors and isomorphisms `u : L ≅ 𝟭`, `l : R ≅ 𝟭`: the unit of
`Adjunction.mapHomologicalComplex` satisfies the same relation, since it is given
degreewise by the unit of `adj`. -/
lemma mapHomologicalComplex_unit_app_comp (X : HomologicalComplex C c) :
    (adj.mapHomologicalComplex c).unit.app X ≫
        (R.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex u.hom c).app X) =
      (NatTrans.mapHomologicalComplex l.inv c).app X := by
  ext n
  simp [h]

section

variable [(HomotopyCategory.quotient C c).IsLocalization
  (HomologicalComplex.homotopyEquivalences C c)]

include h in
/-- The homotopy category form of `Adjunction.mapHomologicalComplex_unit_app_comp`. -/
lemma mapHomotopyCategory_unit_app_comp (Y : HomotopyCategory C c) :
    (adj.mapHomotopyCategory c).unit.app Y ≫
        (R.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory u.hom c).app Y) =
      (NatTrans.mapHomotopyCategory l.inv c).app Y := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hu : (NatTrans.mapHomotopyCategory u.hom c).app
      ((HomotopyCategory.quotient C c).obj X) =
      (HomotopyCategory.quotient C c).map
        ((NatTrans.mapHomologicalComplex u.hom c).app X) := rfl
  have hl : (NatTrans.mapHomotopyCategory l.inv c).app
      ((HomotopyCategory.quotient C c).obj X) =
      (HomotopyCategory.quotient C c).map
        ((NatTrans.mapHomologicalComplex l.inv c).app X) := rfl
  have hmapR : ∀ {P Q : HomologicalComplex C c} (g : P ⟶ Q),
      (R.mapHomotopyCategory c).map ((HomotopyCategory.quotient C c).map g) =
        (HomotopyCategory.quotient C c).map ((R.mapHomologicalComplex c).map g) :=
    fun _ => rfl
  rw [mapHomotopyCategory_unit_app_quotient, hu, hl, hmapR, ← Functor.map_comp,
    mapHomologicalComplex_unit_app_comp c adj u l h]

end

include h in
/-- The bounded below homotopy category form of
`Adjunction.mapHomologicalComplex_unit_app_comp`: if `u : L ≅ 𝟭` and `l : R ≅ 𝟭` satisfy
the unit relation `adj.unit ≫ R(u) = l⁻¹` for an adjunction `L ⊣ R` of endofunctors, then
so do the transformations they induce on the bounded below homotopy categories. -/
lemma mapHomotopyCategoryPlus_unit_app_comp [Limits.HasBinaryBiproducts C]
    (K : HomotopyCategory.Plus C) :
    adj.mapHomotopyCategoryPlus.unit.app K ≫
        R.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus u.hom).app K) =
      (NatTrans.mapHomotopyCategoryPlus l.inv).app K := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmapR : ∀ {P Q : HomotopyCategory.Plus C} (g : P ⟶ Q),
      (HomotopyCategory.Plus.ι C).map (R.mapHomotopyCategoryPlus.map g) =
        (R.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι C).map g) := fun _ => rfl
  have hu : (HomotopyCategory.Plus.ι C).map
      ((NatTrans.mapHomotopyCategoryPlus u.hom).app K) =
      (NatTrans.mapHomotopyCategory u.hom (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  have hl : (HomotopyCategory.Plus.ι C).map
      ((NatTrans.mapHomotopyCategoryPlus l.inv).app K) =
      (NatTrans.mapHomotopyCategory l.inv (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  rw [Functor.map_comp, hmapR, hu, hl, ι_map_mapHomotopyCategoryPlus_unit_app]
  exact mapHomotopyCategory_unit_app_comp (ComplexShape.up ℤ) adj u l h K.obj

end Conjugate

end Adjunction

end CategoryTheory
