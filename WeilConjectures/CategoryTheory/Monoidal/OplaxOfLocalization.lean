/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Oplax monoidal structures through lax monoidal comparison functors

Consider a square of functors
```
        Φ
   K ──────▶ K'
   │          │
 Q │    ≅ c   │ Q'
   ▼          ▼
   D ──────▶ D'
        F
```
where `K, K', D, D'` are monoidal, `Q` and `Q'` are lax monoidal, `Φ` is oplax monoidal, and
`c : Q ⋙ F ≅ Φ ⋙ Q'`. The typical example: `K, K'` homotopy categories, `D, D'` derived
categories with the derived tensor products, `Q, Q'` the localization functors, `Φ` induced by
a monoidal exact functor and `F` its derived functor.

Suppose given maps `δ : F (A ⊗ B) ⟶ F A ⊗ F B` natural in `A, B` and `η : F 𝟙 ⟶ 𝟙`, which
are compatible with the structure maps of `Q, Q', Φ` on the objects of a class `P` of objects
of `K` on which the tensorator of `Q'` (after `Φ`) and the comonoidal structure of `Φ` are
isomorphisms, which is stable
under tensor products, contains `𝟙`, and whose image under `Q` meets every isomorphism class
of `D` (for derived categories: K-flat complexes whose image under `Φ` is K-flat). Then
`δ, η` satisfy the axioms of an oplax monoidal functor
(`CategoryTheory.Functor.OplaxMonoidal.ofLocalization`): the axioms reduce, by naturality, to
objects in the image of `P`, where they follow from the axioms for `Q, Q'` and `Φ`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor

namespace Functor.OplaxMonoidal

variable {K K' D D' : Type*} [Category* K] [Category* K'] [Category* D] [Category* D']
  [MonoidalCategory K] [MonoidalCategory K'] [MonoidalCategory D] [MonoidalCategory D']
  (Q : K ⥤ D) (Q' : K' ⥤ D') [Q.LaxMonoidal] [Q'.LaxMonoidal]
  (Φ : K ⥤ K') [Φ.OplaxMonoidal] (F : D ⥤ D') (c : Q ⋙ F ≅ Φ ⋙ Q')

/-- The data needed to transport an oplax monoidal structure through the square
`c : Q ⋙ F ≅ Φ ⋙ Q'`: the candidate structure maps of `F` and the compatibilities on a
class `P` of good objects. -/
structure LocalizationData where
  /-- The class of good objects. -/
  P : ObjectProperty K
  /-- The candidate comonoidal structure of `F`. -/
  δ (A B : D) : F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B
  δ_natural_left {A A' : D} (f : A ⟶ A') (B : D) :
    F.map (f ▷ B) ≫ δ A' B = δ A B ≫ F.map f ▷ F.obj B
  δ_natural_right (A : D) {B B' : D} (g : B ⟶ B') :
    F.map (A ◁ g) ≫ δ A B' = δ A B ≫ F.obj A ◁ F.map g
  /-- The candidate counit of `F`. -/
  η : F.obj (𝟙_ D) ⟶ 𝟙_ D'
  tensor_mem {X Y : K} : P X → P Y → P (X ⊗ Y)
  unit_mem : P (𝟙_ K)
  essSurj (A : D) : ∃ X, P X ∧ Nonempty (Q.obj X ≅ A)
  isIso_μ' {X Y : K} : P X → P Y → IsIso (LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y))
  isIso_δ {X Y : K} : P X → P Y → IsIso (OplaxMonoidal.δ Φ X Y)
  /-- Compatibility of `δ` with the structure maps on good objects. -/
  fac {X Y : K} : P X → P Y →
    δ (Q.obj X) (Q.obj Y) ≫ (c.hom.app X ⊗ₘ c.hom.app Y) ≫
        LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y) =
      F.map (LaxMonoidal.μ Q X Y) ≫ c.hom.app (X ⊗ Y) ≫ Q'.map (OplaxMonoidal.δ Φ X Y)
  /-- Compatibility of `η` with the structure maps. -/
  fac_η : F.map (LaxMonoidal.ε Q) ≫ c.hom.app (𝟙_ K) ≫ Q'.map (OplaxMonoidal.η Φ) =
    η ≫ LaxMonoidal.ε Q'

variable {Q Q' Φ F c}

namespace LocalizationData

variable (data : LocalizationData Q Q' Φ F c)

/-- Expanding a tensor product of a composite of three morphisms with a morphism. -/
lemma comp_comp_tensorHom {C : Type*} [Category* C] [MonoidalCategory C]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ : C} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (e : X₃ ⟶ X₄) (d : Y₁ ⟶ Y₂) :
    (a ≫ b ≫ e) ⊗ₘ d = a ▷ Y₁ ≫ (b ⊗ₘ d) ≫ e ▷ Y₂ := by
  simp [tensorHom_def, whisker_exchange]

/-- Expanding a tensor product of a morphism with a composite of three morphisms. -/
lemma tensorHom_comp_comp {C : Type*} [Category* C] [MonoidalCategory C]
    {X₁ X₂ Y₁ Y₂ Y₃ Y₄ : C} (d : X₁ ⟶ X₂) (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (e : Y₃ ⟶ Y₄) :
    d ⊗ₘ (a ≫ b ≫ e) = X₁ ◁ a ≫ (d ⊗ₘ b) ≫ X₂ ◁ e := by
  simp [tensorHom_def, whisker_exchange_assoc]

@[reassoc]
lemma δ_natural_left' {A A' : D} (f : A ⟶ A') (B : D) :
    F.map (f ▷ B) ≫ data.δ A' B = data.δ A B ≫ F.map f ▷ F.obj B :=
  data.δ_natural_left f B

@[reassoc]
lemma δ_natural_right' (A : D) {B B' : D} (g : B ⟶ B') :
    F.map (A ◁ g) ≫ data.δ A B' = data.δ A B ≫ F.obj A ◁ F.map g :=
  data.δ_natural_right A g

/-- Naturality of `δ` with respect to `⊗ₘ`. -/
@[reassoc]
lemma δ_natural {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B') :
    F.map (f ⊗ₘ g) ≫ data.δ A' B' = data.δ A B ≫ (F.map f ⊗ₘ F.map g) := by
  rw [tensorHom_def, F.map_comp, Category.assoc, data.δ_natural_right,
    data.δ_natural_left'_assoc, tensorHom_def]

lemma fac_assoc_left {X Y Z : K} (hX : data.P X) (hY : data.P Y) (hZ : data.P Z) :
    data.δ (Q.obj X ⊗ Q.obj Y) (Q.obj Z) ≫
        ((data.δ (Q.obj X) (Q.obj Y) ≫ (c.hom.app X ⊗ₘ c.hom.app Y) ≫
          LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y)) ⊗ₘ c.hom.app Z) ≫
        LaxMonoidal.μ Q' (Φ.obj X ⊗ Φ.obj Y) (Φ.obj Z) =
      F.map (LaxMonoidal.μ Q X Y ▷ Q.obj Z ≫ LaxMonoidal.μ Q (X ⊗ Y) Z) ≫ c.hom.app _ ≫
        Q'.map (OplaxMonoidal.δ Φ (X ⊗ Y) Z ≫ OplaxMonoidal.δ Φ X Y ▷ Φ.obj Z) := by
  rw [data.fac hX hY, comp_comp_tensorHom]
  simp only [Functor.comp_obj, Category.assoc]
  rw [LaxMonoidal.μ_natural_left, ← data.δ_natural_left'_assoc,
    reassoc_of% (data.fac (data.tensor_mem hX hY) hZ)]
  simp

lemma fac_assoc_right {X Y Z : K} (hX : data.P X) (hY : data.P Y) (hZ : data.P Z) :
    data.δ (Q.obj X) (Q.obj Y ⊗ Q.obj Z) ≫
        (c.hom.app X ⊗ₘ (data.δ (Q.obj Y) (Q.obj Z) ≫ (c.hom.app Y ⊗ₘ c.hom.app Z) ≫
          LaxMonoidal.μ Q' (Φ.obj Y) (Φ.obj Z))) ≫
        LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y ⊗ Φ.obj Z) =
      F.map (Q.obj X ◁ LaxMonoidal.μ Q Y Z ≫ LaxMonoidal.μ Q X (Y ⊗ Z)) ≫ c.hom.app _ ≫
        Q'.map (OplaxMonoidal.δ Φ X (Y ⊗ Z) ≫ Φ.obj X ◁ OplaxMonoidal.δ Φ Y Z) := by
  rw [data.fac hY hZ, tensorHom_comp_comp]
  simp only [Functor.comp_obj, Category.assoc]
  rw [LaxMonoidal.μ_natural_right, ← data.δ_natural_right'_assoc,
    reassoc_of% (data.fac hX (data.tensor_mem hY hZ))]
  simp

lemma isIso_μ'_tensor {X Y Z : K} (hX : data.P X) (hY : data.P Y) (hZ : data.P Z) :
    IsIso (LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y ⊗ Φ.obj Z)) := by
  have := data.isIso_μ' hX (data.tensor_mem hY hZ)
  have := data.isIso_δ hY hZ
  rw [(IsIso.eq_inv_comp _).mpr
    (LaxMonoidal.μ_natural_right Q' (Φ.obj X) (OplaxMonoidal.δ Φ Y Z))]
  infer_instance

lemma associativity_of_good {X Y Z : K} (hX : data.P X) (hY : data.P Y) (hZ : data.P Z) :
    data.δ (Q.obj X ⊗ Q.obj Y) (Q.obj Z) ≫ data.δ (Q.obj X) (Q.obj Y) ▷ F.obj (Q.obj Z) ≫
        (α_ (F.obj (Q.obj X)) (F.obj (Q.obj Y)) (F.obj (Q.obj Z))).hom =
      F.map (α_ (Q.obj X) (Q.obj Y) (Q.obj Z)).hom ≫ data.δ (Q.obj X) (Q.obj Y ⊗ Q.obj Z) ≫
        F.obj (Q.obj X) ◁ data.δ (Q.obj Y) (Q.obj Z) := by
  have := data.isIso_μ' hY hZ
  have := data.isIso_μ'_tensor hX hY hZ
  rw [← cancel_mono ((c.hom.app X ⊗ₘ (c.hom.app Y ⊗ₘ c.hom.app Z)) ≫
    Q'.obj (Φ.obj X) ◁ LaxMonoidal.μ Q' (Φ.obj Y) (Φ.obj Z) ≫
    LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y ⊗ Φ.obj Z))]
  calc _ = (data.δ (Q.obj X ⊗ Q.obj Y) (Q.obj Z) ≫
        ((data.δ (Q.obj X) (Q.obj Y) ≫ (c.hom.app X ⊗ₘ c.hom.app Y) ≫
          LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y)) ⊗ₘ c.hom.app Z) ≫
        LaxMonoidal.μ Q' (Φ.obj X ⊗ Φ.obj Y) (Φ.obj Z)) ≫ Q'.map (α_ _ _ _).hom := by
        rw [comp_comp_tensorHom]
        simp only [Functor.comp_obj, Category.assoc, LaxMonoidal.associativity,
          associator_naturality_assoc]
    _ = F.map (α_ (Q.obj X) (Q.obj Y) (Q.obj Z)).hom ≫ data.δ (Q.obj X) (Q.obj Y ⊗ Q.obj Z) ≫
        (c.hom.app X ⊗ₘ (data.δ (Q.obj Y) (Q.obj Z) ≫ (c.hom.app Y ⊗ₘ c.hom.app Z) ≫
          LaxMonoidal.μ Q' (Φ.obj Y) (Φ.obj Z))) ≫
        LaxMonoidal.μ Q' (Φ.obj X) (Φ.obj Y ⊗ Φ.obj Z) := by
        rw [data.fac_assoc_left hX hY hZ, data.fac_assoc_right hX hY hZ]
        have h₁ := c.hom.naturality (α_ X Y Z).hom
        have h₂ := Q'.congr_map (OplaxMonoidal.associativity Φ X Y Z)
        dsimp at h₁
        simp only [Functor.map_comp, Category.assoc] at h₂ ⊢
        rw [h₂, ← reassoc_of% h₁]
        simp only [← F.map_comp_assoc, LaxMonoidal.associativity]
    _ = _ := by
        rw [tensorHom_comp_comp]
        simp

lemma left_unitality_of_good {X : K} (hX : data.P X) :
    F.map (λ_ (Q.obj X)).inv ≫ data.δ (𝟙_ D) (Q.obj X) ≫ data.η ▷ F.obj (Q.obj X) =
      (λ_ (F.obj (Q.obj X))).inv := by
  rw [← cancel_mono (𝟙_ D' ◁ c.hom.app X ≫ (λ_ _).hom)]
  calc _ = F.map (λ_ (Q.obj X)).inv ≫ data.δ (𝟙_ D) (Q.obj X) ≫
        ((data.η ≫ LaxMonoidal.ε Q') ⊗ₘ c.hom.app X) ≫
        LaxMonoidal.μ Q' (𝟙_ K') (Φ.obj X) ≫ Q'.map (λ_ _).hom := by
        simp only [Functor.comp_obj]
        rw [LaxMonoidal.left_unitality Q' (Φ.obj X), tensorHom_def, comp_whiskerRight]
        simp only [Category.assoc, whisker_exchange_assoc]
    _ = F.map ((λ_ (Q.obj X)).inv ≫ LaxMonoidal.ε Q ▷ Q.obj X ≫
          LaxMonoidal.μ Q (𝟙_ K) X) ≫ c.hom.app _ ≫
        Q'.map (OplaxMonoidal.δ Φ (𝟙_ K) X ≫ OplaxMonoidal.η Φ ▷ Φ.obj X ≫ (λ_ _).hom) := by
        rw [← data.fac_η, comp_comp_tensorHom]
        simp only [Functor.comp_obj, Category.assoc, LaxMonoidal.μ_natural_left_assoc]
        rw [← data.δ_natural_left'_assoc, reassoc_of% (data.fac data.unit_mem hX)]
        simp only [Functor.map_comp, Category.assoc]
    _ = c.hom.app X := by
        rw [LaxMonoidal.left_unitality_inv, OplaxMonoidal.left_unitality_hom]
        have := c.hom.naturality (λ_ X).inv
        dsimp at this
        rw [reassoc_of% this, ← Q'.map_comp, ← Φ.map_comp, Iso.inv_hom_id, Φ.map_id, Q'.map_id,
          Category.comp_id]
    _ = _ := by rw [← leftUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

lemma right_unitality_of_good {X : K} (hX : data.P X) :
    F.map (ρ_ (Q.obj X)).inv ≫ data.δ (Q.obj X) (𝟙_ D) ≫ F.obj (Q.obj X) ◁ data.η =
      (ρ_ (F.obj (Q.obj X))).inv := by
  rw [← cancel_mono (c.hom.app X ▷ 𝟙_ D' ≫ (ρ_ _).hom)]
  calc _ = F.map (ρ_ (Q.obj X)).inv ≫ data.δ (Q.obj X) (𝟙_ D) ≫
        (c.hom.app X ⊗ₘ (data.η ≫ LaxMonoidal.ε Q')) ≫
        LaxMonoidal.μ Q' (Φ.obj X) (𝟙_ K') ≫ Q'.map (ρ_ _).hom := by
        simp only [Functor.comp_obj]
        rw [LaxMonoidal.right_unitality Q' (Φ.obj X), tensorHom_def',
          MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc, whisker_exchange_assoc]
    _ = F.map ((ρ_ (Q.obj X)).inv ≫ Q.obj X ◁ LaxMonoidal.ε Q ≫
          LaxMonoidal.μ Q X (𝟙_ K)) ≫ c.hom.app _ ≫
        Q'.map (OplaxMonoidal.δ Φ X (𝟙_ K) ≫ Φ.obj X ◁ OplaxMonoidal.η Φ ≫ (ρ_ _).hom) := by
        rw [← data.fac_η, tensorHom_comp_comp]
        simp only [Functor.comp_obj, Category.assoc, LaxMonoidal.μ_natural_right_assoc]
        rw [← data.δ_natural_right'_assoc, reassoc_of% (data.fac hX data.unit_mem)]
        simp only [Functor.map_comp, Category.assoc]
    _ = c.hom.app X := by
        rw [LaxMonoidal.right_unitality_inv, OplaxMonoidal.right_unitality_hom]
        have := c.hom.naturality (ρ_ X).inv
        dsimp at this
        rw [reassoc_of% this, ← Q'.map_comp, ← Φ.map_comp, Iso.inv_hom_id, Φ.map_id, Q'.map_id,
          Category.comp_id]
    _ = _ := by rw [← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Naturality of the left hand side of the oplax associativity axiom. -/
lemma associativity_lhs_natural {A B C A' B' C' : D} (a : A ⟶ A') (b : B ⟶ B') (e : C ⟶ C') :
    F.map ((a ⊗ₘ b) ⊗ₘ e) ≫ data.δ (A' ⊗ B') C' ≫ data.δ A' B' ▷ F.obj C' ≫
        (α_ (F.obj A') (F.obj B') (F.obj C')).hom =
      (data.δ (A ⊗ B) C ≫ data.δ A B ▷ F.obj C ≫ (α_ (F.obj A) (F.obj B) (F.obj C)).hom) ≫
        (F.map a ⊗ₘ (F.map b ⊗ₘ F.map e)) := by
  rw [data.δ_natural_assoc, tensorHom_comp_whiskerRight_assoc, data.δ_natural,
    ← whiskerRight_comp_tensorHom_assoc, associator_naturality]
  simp only [Category.assoc]

/-- Naturality of the right hand side of the oplax associativity axiom. -/
lemma associativity_rhs_natural {A B C A' B' C' : D} (a : A ⟶ A') (b : B ⟶ B') (e : C ⟶ C') :
    F.map ((a ⊗ₘ b) ⊗ₘ e) ≫ F.map (α_ A' B' C').hom ≫ data.δ A' (B' ⊗ C') ≫
        F.obj A' ◁ data.δ B' C' =
      (F.map (α_ A B C).hom ≫ data.δ A (B ⊗ C) ≫ F.obj A ◁ data.δ B C) ≫
        (F.map a ⊗ₘ (F.map b ⊗ₘ F.map e)) := by
  rw [← F.map_comp_assoc, associator_naturality, F.map_comp_assoc, data.δ_natural_assoc,
    tensorHom_comp_whiskerLeft, data.δ_natural, ← whiskerLeft_comp_tensorHom]
  simp only [Category.assoc]

/-- The oplax associativity axiom is invariant under isomorphisms. -/
lemma associativity_of_iso {A B C A' B' C' : D} (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C')
    (h : data.δ (A ⊗ B) C ≫ data.δ A B ▷ F.obj C ≫ (α_ (F.obj A) (F.obj B) (F.obj C)).hom =
      F.map (α_ A B C).hom ≫ data.δ A (B ⊗ C) ≫ F.obj A ◁ data.δ B C) :
    data.δ (A' ⊗ B') C' ≫ data.δ A' B' ▷ F.obj C' ≫ (α_ (F.obj A') (F.obj B') (F.obj C')).hom =
      F.map (α_ A' B' C').hom ≫ data.δ A' (B' ⊗ C') ≫ F.obj A' ◁ data.δ B' C' := by
  rw [← cancel_epi (F.map ((eA.hom ⊗ₘ eB.hom) ⊗ₘ eC.hom)), data.associativity_lhs_natural, h,
    data.associativity_rhs_natural]

/-- The oplax left unitality axiom is invariant under isomorphisms. -/
lemma left_unitality_of_iso {A A' : D} (e : A ≅ A')
    (h : F.map (λ_ A).inv ≫ data.δ (𝟙_ D) A ≫ data.η ▷ F.obj A = (λ_ (F.obj A)).inv) :
    F.map (λ_ A').inv ≫ data.δ (𝟙_ D) A' ≫ data.η ▷ F.obj A' = (λ_ (F.obj A')).inv := by
  rw [← cancel_epi (F.map e.hom), ← F.map_comp_assoc, leftUnitor_inv_naturality, F.map_comp_assoc,
    data.δ_natural_right'_assoc, whisker_exchange, reassoc_of% h, leftUnitor_inv_naturality]

/-- The oplax right unitality axiom is invariant under isomorphisms. -/
lemma right_unitality_of_iso {A A' : D} (e : A ≅ A')
    (h : F.map (ρ_ A).inv ≫ data.δ A (𝟙_ D) ≫ F.obj A ◁ data.η = (ρ_ (F.obj A)).inv) :
    F.map (ρ_ A').inv ≫ data.δ A' (𝟙_ D) ≫ F.obj A' ◁ data.η = (ρ_ (F.obj A')).inv := by
  rw [← cancel_epi (F.map e.hom), ← F.map_comp_assoc, rightUnitor_inv_naturality,
    F.map_comp_assoc, data.δ_natural_left'_assoc, ← whisker_exchange, reassoc_of% h,
    rightUnitor_inv_naturality]

end LocalizationData

/-- The oplax monoidal structure on `F` obtained from `LocalizationData`. -/
@[instance_reducible]
noncomputable def ofLocalization (data : LocalizationData Q Q' Φ F c) : F.OplaxMonoidal where
  δ := data.δ
  η := data.η
  δ_natural_left f B := (data.δ_natural_left f B).symm
  δ_natural_right A g := (data.δ_natural_right A g).symm
  oplax_associativity A B C := by
    obtain ⟨X, hX, ⟨eA⟩⟩ := data.essSurj A
    obtain ⟨Y, hY, ⟨eB⟩⟩ := data.essSurj B
    obtain ⟨Z, hZ, ⟨eC⟩⟩ := data.essSurj C
    exact data.associativity_of_iso eA eB eC (data.associativity_of_good hX hY hZ)
  oplax_left_unitality A := by
    obtain ⟨X, hX, ⟨e⟩⟩ := data.essSurj A
    exact (data.left_unitality_of_iso e (data.left_unitality_of_good hX)).symm
  oplax_right_unitality A := by
    obtain ⟨X, hX, ⟨e⟩⟩ := data.essSurj A
    exact (data.right_unitality_of_iso e (data.right_unitality_of_good hX)).symm

@[simp]
lemma ofLocalization_δ (data : LocalizationData Q Q' Φ F c) (A B : D) :
    letI := ofLocalization data
    OplaxMonoidal.δ F A B = data.δ A B :=
  rfl

@[simp]
lemma ofLocalization_η (data : LocalizationData Q Q' Φ F c) :
    letI := ofLocalization data
    OplaxMonoidal.η F = data.η :=
  rfl

end Functor.OplaxMonoidal

namespace Functor.Monoidal

variable {K K' D D' : Type*} [Category* K] [Category* K'] [Category* D] [Category* D']
  [MonoidalCategory K] [MonoidalCategory K'] [MonoidalCategory D] [MonoidalCategory D']
  {Q : K ⥤ D} {Q' : K' ⥤ D'} [Q.LaxMonoidal] [Q'.LaxMonoidal]
  {Φ : K ⥤ K'} [Φ.OplaxMonoidal] {F : D ⥤ D'} {c : Q ⋙ F ≅ Φ ⋙ Q'}

/-- The monoidal structure on `F` obtained from `LocalizationData` whose structure maps are
isomorphisms. -/
@[instance_reducible]
noncomputable def ofLocalization (data : OplaxMonoidal.LocalizationData Q Q' Φ F c)
    [∀ A B, IsIso (data.δ A B)] [IsIso data.η] : F.Monoidal :=
  letI := OplaxMonoidal.ofLocalization data
  haveI : ∀ A B, IsIso (OplaxMonoidal.δ F A B) := fun A B ↦ inferInstanceAs (IsIso (data.δ A B))
  haveI : IsIso (OplaxMonoidal.η F) := inferInstanceAs (IsIso data.η)
  Monoidal.ofOplaxMonoidal F

@[simp]
lemma ofLocalization_δ (data : OplaxMonoidal.LocalizationData Q Q' Φ F c)
    [∀ A B, IsIso (data.δ A B)] [IsIso data.η] (A B : D) :
    letI := ofLocalization data
    OplaxMonoidal.δ F A B = data.δ A B :=
  rfl

@[simp]
lemma ofLocalization_η (data : OplaxMonoidal.LocalizationData Q Q' Φ F c)
    [∀ A B, IsIso (data.δ A B)] [IsIso data.η] :
    letI := ofLocalization data
    OplaxMonoidal.η F = data.η :=
  rfl

end Functor.Monoidal

end CategoryTheory
