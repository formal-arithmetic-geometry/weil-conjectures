/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated

/-!
# The octahedral axiom in the Karoubi envelope

Let `C` be a triangulated category. We show that the Karoubi envelope `Karoubi C` satisfies the
octahedral axiom (blueprint `lem-weil-karoubi-envelope-triangulated`).

Given composable morphisms `(X₁, p₁) ⟶ (X₂, p₂) ⟶ (X₃, p₃)` of the envelope, represented by
`u : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in `C`, choose cones `Z₁₂`, `Z₂₃`, `Z₁₃` of `u`, `g`, `u ≫ g`
in `C` with idempotent endomorphisms `s₁₂`, `s₂₃`, `s₁₃` extending the `pᵢ`
(`CategoryTheory.Pretriangulated.exists_idempotent_of_distTriang`), and an octahedron
`Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` in `C`. The complementary triangles, with idempotents
`𝟙 - pᵢ` and `𝟙 - s`, are triangles on zero morphisms, hence split. Using these splittings one
writes down explicit corrections `x` and `y` such that the triangle
`(Z₁₂, s₁₂) ⟶ (Z₁₃, s₁₃) ⟶ (Z₂₃, s₂₃) ⟶ (Z₁₂, s₁₂)⟦1⟧` of the envelope is a retract of the image
of the octahedron triangle, hence distinguished.

This file contains the algebraic part of the argument, in `C`.
-/

@[expose] public section

namespace CategoryTheory.Idempotents.Karoubi.OctahedronAux

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

lemma comp_compl {X Y : C} {v : X ⟶ Y} {p : X ⟶ X} {s : Y ⟶ Y} (h : v ≫ s = p ≫ v) :
    v ≫ (𝟙 _ - s) = (𝟙 _ - p) ≫ v := by
  simp [comp_sub, sub_comp, h]

lemma compl_comp_self {X : C} {s : X ⟶ X} (hs : s ≫ s = s) : (𝟙 _ - s) ≫ s = 0 := by
  simp [sub_comp, hs]

lemma self_comp_compl {X : C} {s : X ⟶ X} (hs : s ≫ s = s) : s ≫ (𝟙 _ - s) = 0 := by
  simp [comp_sub, hs]

lemma compl_comp_compl {X : C} {s : X ⟶ X} (hs : s ≫ s = s) :
    (𝟙 _ - s) ≫ (𝟙 _ - s) = 𝟙 _ - s := by
  simp [comp_sub, sub_comp, hs]

lemma comm_of_comp_eq' {X Y : C} {p : X ⟶ X} {q : Y ⟶ Y} (f : X ⟶ Y) (hq : q ≫ q = q)
    (h : f ≫ q = p ≫ f) : p ≫ (f ≫ q) ≫ q = f ≫ q := by
  rw [assoc, hq, ← assoc, ← h, assoc, hq]

lemma compl_comp {X Y : C} {w : X ⟶ Y} {s : X ⟶ X} {q : Y ⟶ Y} (h : s ≫ w = w ≫ q) :
    (𝟙 _ - s) ≫ w = w ≫ (𝟙 _ - q) := by
  simp [comp_sub, sub_comp, h]

section Algebra

variable {X₁ X₂ X₃ Y₁ Y₂ Z₁₂ Z₁₃ Z₂₃ : C}
  {p₂ : X₂ ⟶ X₂} {p₃ : X₃ ⟶ X₃} {q₁ : Y₁ ⟶ Y₁} {q₂ : Y₂ ⟶ Y₂}
  {s₁₂ : Z₁₂ ⟶ Z₁₂} {s₁₃ : Z₁₃ ⟶ Z₁₃} {s₂₃ : Z₂₃ ⟶ Z₂₃}
  {g : X₂ ⟶ X₃} {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ Y₁} {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ Y₁}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ Y₂} {u₁ : Y₁ ⟶ Y₂}
  {m₁ : Z₁₂ ⟶ Z₁₃} {m₃ : Z₁₃ ⟶ Z₂₃}
  {ρ₁₂ : Z₁₂ ⟶ X₂} {σ₁₂ : Y₁ ⟶ Z₁₂} {ρ₁₃ : Z₁₃ ⟶ X₃} {σ₁₃ : Y₁ ⟶ Z₁₃}
  {ρ₂₃ : Z₂₃ ⟶ X₃} {σ₂₃ : Y₂ ⟶ Z₂₃}

/-- The correction `x : Z₁₃ ⟶ Z₁₃` of the inclusion of `(Z₁₃, s₁₃)`. -/
def corrX (s₁₃ : Z₁₃ ⟶ Z₁₃) (m₃ : Z₁₃ ⟶ Z₂₃) (s₂₃ : Z₂₃ ⟶ Z₂₃) (ρ₂₃ : Z₂₃ ⟶ X₃)
    (v₁₃ : X₃ ⟶ Z₁₃) : Z₁₃ ⟶ Z₁₃ :=
  -(s₁₃ ≫ m₃ ≫ (𝟙 _ - s₂₃) ≫ ρ₂₃ ≫ v₁₃ ≫ (𝟙 _ - s₁₃))

/-- The correction `y : Z₁₃ ⟶ Z₁₃` of the projection onto `(Z₁₃, s₁₃)`. -/
def corrY (s₁₃ : Z₁₃ ⟶ Z₁₃) (w₁₃ : Z₁₃ ⟶ Y₁) (σ₁₂ : Y₁ ⟶ Z₁₂) (m₁ : Z₁₂ ⟶ Z₁₃) :
    Z₁₃ ⟶ Z₁₃ :=
  -((𝟙 _ - s₁₃) ≫ w₁₃ ≫ σ₁₂ ≫ m₁ ≫ s₁₃)

lemma m₁_corrY (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) (hg₂ : p₂ ≫ g = g)
    (hv₁₂ : v₁₂ ≫ s₁₂ = p₂ ≫ v₁₂) (hw₁₃ : s₁₃ ≫ w₁₃ = w₁₃ ≫ q₁)
    (c₁ : v₁₂ ≫ m₁ = g ≫ v₁₃) (c₂ : m₁ ≫ w₁₃ = w₁₂)
    (S₁₂ : ρ₁₂ ≫ v₁₂ ≫ (𝟙 _ - s₁₂) + w₁₂ ≫ (𝟙 _ - q₁) ≫ σ₁₂ = 𝟙 _ - s₁₂) :
    m₁ ≫ corrY s₁₃ w₁₃ σ₁₂ m₁ = -((𝟙 _ - s₁₂) ≫ m₁ ≫ s₁₃) := by
  rw [corrY, comp_neg, neg_inj, ← S₁₂, add_comp]
  have h0 : (𝟙 _ - p₂) ≫ g = 0 := by rw [sub_comp, id_comp, hg₂, sub_self]
  rw [assoc, assoc, reassoc_of% (comp_compl hv₁₂), reassoc_of% c₁, reassoc_of% h0, zero_comp,
    comp_zero, zero_add, reassoc_of% (compl_comp hw₁₃), reassoc_of% c₂]
  simp only [assoc]

lemma compl_m₃_eq (hp₃ : p₃ ≫ p₃ = p₃) (hv₁₃ : v₁₃ ≫ s₁₃ = p₃ ≫ v₁₃) (c₃ : v₁₃ ≫ m₃ = v₂₃)
    (hv₂₃ : v₂₃ ≫ s₂₃ = p₃ ≫ v₂₃)
    (S₁₃ : ρ₁₃ ≫ v₁₃ ≫ (𝟙 _ - s₁₃) + w₁₃ ≫ (𝟙 _ - q₁) ≫ σ₁₃ = 𝟙 _ - s₁₃) :
    (𝟙 _ - s₁₃) ≫ m₃ ≫ s₂₃ = w₁₃ ≫ (𝟙 _ - q₁) ≫ σ₁₃ ≫ m₃ ≫ s₂₃ := by
  have e2 : v₁₃ ≫ (𝟙 _ - s₁₃) ≫ m₃ ≫ s₂₃ = 0 := by
    rw [reassoc_of% (comp_compl hv₁₃), reassoc_of% c₃, hv₂₃, reassoc_of% (compl_comp_self hp₃),
      zero_comp]
  conv_lhs => rw [← S₁₃]
  rw [add_comp, assoc, assoc, e2, comp_zero, zero_add]
  simp only [assoc]

lemma corrY_m₃ (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) (hp₃ : p₃ ≫ p₃ = p₃) (hq₁ : q₁ ≫ q₁ = q₁)
    (hv₁₃ : v₁₃ ≫ s₁₃ = p₃ ≫ v₁₃) (hw₁₃ : s₁₃ ≫ w₁₃ = w₁₃ ≫ q₁)
    (hv₂₃ : v₂₃ ≫ s₂₃ = p₃ ≫ v₂₃) (c₂ : m₁ ≫ w₁₃ = w₁₂) (c₃ : v₁₃ ≫ m₃ = v₂₃)
    (hmm : m₁ ≫ m₃ = 0)
    (S₁₃ : ρ₁₃ ≫ v₁₃ ≫ (𝟙 _ - s₁₃) + w₁₃ ≫ (𝟙 _ - q₁) ≫ σ₁₃ = 𝟙 _ - s₁₃)
    (T₁₂ : σ₁₂ ≫ w₁₂ ≫ (𝟙 _ - q₁) = 𝟙 _ - q₁) :
    corrY s₁₃ w₁₃ σ₁₂ m₁ ≫ s₁₃ ≫ m₃ ≫ s₂₃ = (𝟙 _ - s₁₃) ≫ m₃ ≫ s₂₃ := by
  have e1 : m₁ ≫ s₁₃ ≫ m₃ ≫ s₂₃ = -(m₁ ≫ (𝟙 _ - s₁₃) ≫ m₃ ≫ s₂₃) := by
    rw [sub_comp, comp_sub, id_comp, reassoc_of% hmm, zero_comp, zero_sub, neg_neg]
  have e3 := compl_m₃_eq hp₃ hv₁₃ c₃ hv₂₃ S₁₃
  rw [corrY, neg_comp]
  simp only [assoc, reassoc_of% hs₁₃]
  rw [e1, comp_neg, comp_neg, comp_neg, neg_neg, e3, reassoc_of% c₂,
    reassoc_of% (compl_comp hw₁₃), reassoc_of% T₁₂, reassoc_of% (compl_comp_compl hq₁)]

lemma corrX_m₃ (hs₂₃ : s₂₃ ≫ s₂₃ = s₂₃) (hv₁₃ : v₁₃ ≫ s₁₃ = p₃ ≫ v₁₃)
    (hv₂₃ : v₂₃ ≫ s₂₃ = p₃ ≫ v₂₃) (c₃ : v₁₃ ≫ m₃ = v₂₃) (c₄ : w₁₃ ≫ u₁ = m₃ ≫ w₂₃)
    (hu₁ : u₁ ≫ (𝟙 _ - q₂) = 0) (hρ₂₃ : (𝟙 _ - s₂₃) ≫ ρ₂₃ = ρ₂₃)
    (S₂₃ : ρ₂₃ ≫ v₂₃ ≫ (𝟙 _ - s₂₃) + w₂₃ ≫ (𝟙 _ - q₂) ≫ σ₂₃ = 𝟙 _ - s₂₃) :
    corrX s₁₃ m₃ s₂₃ ρ₂₃ v₁₃ ≫ m₃ = -(s₁₃ ≫ m₃ ≫ (𝟙 _ - s₂₃)) := by
  have f1 : v₁₃ ≫ (𝟙 _ - s₁₃) ≫ m₃ = v₂₃ ≫ (𝟙 _ - s₂₃) := by
    rw [reassoc_of% (comp_compl hv₁₃), c₃, comp_compl hv₂₃]
  have f2 : s₁₃ ≫ m₃ ≫ ρ₂₃ ≫ v₂₃ ≫ (𝟙 _ - s₂₃) = s₁₃ ≫ m₃ ≫ (𝟙 _ - s₂₃) := by
    have := congrArg (fun t ↦ s₁₃ ≫ m₃ ≫ t) S₂₃
    simp only [comp_add, ← reassoc_of% c₄, reassoc_of% hu₁, zero_comp, comp_zero,
      add_zero] at this
    exact this
  rw [corrX, neg_comp, neg_inj]
  simp only [assoc]
  rw [f1, reassoc_of% hρ₂₃, f2]

lemma s_m₁_compl (hq₁ : q₁ ≫ q₁ = q₁) (hw₁₂ : s₁₂ ≫ w₁₂ = w₁₂ ≫ q₁) (c₂ : m₁ ≫ w₁₃ = w₁₂)
    (S₁₃ : ρ₁₃ ≫ v₁₃ ≫ (𝟙 _ - s₁₃) + w₁₃ ≫ (𝟙 _ - q₁) ≫ σ₁₃ = 𝟙 _ - s₁₃) :
    s₁₂ ≫ m₁ ≫ (𝟙 _ - s₁₃) = s₁₂ ≫ m₁ ≫ ρ₁₃ ≫ v₁₃ ≫ (𝟙 _ - s₁₃) := by
  conv_lhs => rw [← S₁₃]
  rw [comp_add, comp_add, reassoc_of% c₂, reassoc_of% hw₁₂, reassoc_of% (self_comp_compl hq₁),
    zero_comp, comp_zero, add_zero]

lemma m₁_corrX (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) (hs₂₃ : s₂₃ ≫ s₂₃ = s₂₃) (hq₁ : q₁ ≫ q₁ = q₁)
    (hw₁₂ : s₁₂ ≫ w₁₂ = w₁₂ ≫ q₁) (hv₁₃ : v₁₃ ≫ s₁₃ = p₃ ≫ v₁₃)
    (hv₂₃ : v₂₃ ≫ s₂₃ = p₃ ≫ v₂₃) (c₂ : m₁ ≫ w₁₃ = w₁₂) (c₃ : v₁₃ ≫ m₃ = v₂₃)
    (hmm : m₁ ≫ m₃ = 0)
    (S₁₃ : ρ₁₃ ≫ v₁₃ ≫ (𝟙 _ - s₁₃) + w₁₃ ≫ (𝟙 _ - q₁) ≫ σ₁₃ = 𝟙 _ - s₁₃)
    (T₂₃ : v₂₃ ≫ (𝟙 _ - s₂₃) ≫ ρ₂₃ = 𝟙 _ - p₃) :
    s₁₂ ≫ m₁ ≫ s₁₃ ≫ corrX s₁₃ m₃ s₂₃ ρ₂₃ v₁₃ = s₁₂ ≫ m₁ ≫ (𝟙 _ - s₁₃) := by
  have e1 : ∀ {W : C} (h : Z₂₃ ⟶ W), m₁ ≫ s₁₃ ≫ m₃ ≫ h = -(m₁ ≫ (𝟙 _ - s₁₃) ≫ m₃ ≫ h) := by
    intro W h
    rw [sub_comp, comp_sub, id_comp, reassoc_of% hmm, zero_comp, zero_sub, neg_neg]
  have f1 : v₁₃ ≫ (𝟙 _ - s₁₃) ≫ m₃ = v₂₃ ≫ (𝟙 _ - s₂₃) := by
    rw [reassoc_of% (comp_compl hv₁₃), c₃, comp_compl hv₂₃]
  have hs := s_m₁_compl hq₁ hw₁₂ c₂ S₁₃
  rw [corrX]
  simp only [comp_neg, reassoc_of% hs₁₃]
  rw [e1, comp_neg, neg_neg, reassoc_of% hs, reassoc_of% f1, reassoc_of% (compl_comp_compl hs₂₃),
    reassoc_of% T₂₃, ← reassoc_of% (comp_compl hv₁₃), compl_comp_compl hs₁₃, hs]

lemma corrX_corrY (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) (hw₁₃ : s₁₃ ≫ w₁₃ = w₁₃ ≫ q₁)
    (hvw : v₁₃ ≫ w₁₃ = 0) :
    corrX s₁₃ m₃ s₂₃ ρ₂₃ v₁₃ ≫ corrY s₁₃ w₁₃ σ₁₂ m₁ = 0 := by
  rw [corrX, corrY, neg_comp, comp_neg, neg_neg]
  simp only [assoc]
  rw [reassoc_of% (compl_comp_compl hs₁₃), reassoc_of% (compl_comp hw₁₃), reassoc_of% hvw,
    zero_comp, comp_zero, comp_zero, comp_zero, comp_zero]

lemma s_corrX (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) :
    s₁₃ ≫ corrX s₁₃ m₃ s₂₃ ρ₂₃ v₁₃ = corrX s₁₃ m₃ s₂₃ ρ₂₃ v₁₃ := by
  rw [corrX, comp_neg, reassoc_of% hs₁₃]

lemma corrX_s (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) : corrX s₁₃ m₃ s₂₃ ρ₂₃ v₁₃ ≫ s₁₃ = 0 := by
  rw [corrX, neg_comp]
  simp only [assoc, compl_comp_self hs₁₃, comp_zero, neg_zero]

lemma corrY_s (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) :
    corrY s₁₃ w₁₃ σ₁₂ m₁ ≫ s₁₃ = corrY s₁₃ w₁₃ σ₁₂ m₁ := by
  rw [corrY, neg_comp]
  simp only [assoc, hs₁₃]

lemma s_corrY (hs₁₃ : s₁₃ ≫ s₁₃ = s₁₃) : s₁₃ ≫ corrY s₁₃ w₁₃ σ₁₂ m₁ = 0 := by
  rw [corrY, comp_neg, reassoc_of% (self_comp_compl hs₁₃), zero_comp, neg_zero]

end Algebra

end CategoryTheory.Idempotents.Karoubi.OctahedronAux

namespace CategoryTheory.Idempotents.Karoubi

open Category Limits Preadditive ZeroObject Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

section Raw

variable {X₁ X₂ X₃ : C} (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
  (p₁ : X₁ ⟶ X₁) (p₂ : X₂ ⟶ X₂) (p₃ : X₃ ⟶ X₃) (h₁ : p₁ ≫ p₁ = p₁) (h₂ : p₂ ≫ p₂ = p₂)
  (h₃ : p₃ ≫ p₃ = p₃) (c₁ : u ≫ p₂ = p₁ ≫ u) (c₂ : v ≫ p₃ = p₂ ≫ v)
  (c₃ : w ≫ p₁⟦(1 : ℤ)⟧' = p₃ ≫ w)

/-- The triangle `(X₁, p₁) ⟶ (X₂, p₂) ⟶ (X₃, p₃) ⟶ (X₁, p₁)⟦1⟧` of the Karoubi envelope
attached to a triangle of `C` with compatible idempotents. -/
@[simps!]
noncomputable def triangleOfIdem' : Triangle (Karoubi C) :=
  Triangle.mk (X := ⟨X₁, p₁, h₁⟩) (Y := ⟨X₂, p₂, h₂⟩) (Z := ⟨X₃, p₃, h₃⟩)
    ⟨u ≫ p₂, OctahedronAux.comm_of_comp_eq' u h₂ c₁⟩
    ⟨v ≫ p₃, OctahedronAux.comm_of_comp_eq' v h₃ c₂⟩
    ⟨w ≫ p₁⟦(1 : ℤ)⟧', OctahedronAux.comm_of_comp_eq' w
      (by rw [← Functor.map_comp, h₁]) c₃⟩

lemma triangleOfIdem'_distinguished (hT : Triangle.mk u v w ∈ distTriang C) :
    triangleOfIdem' u v w p₁ p₂ p₃ h₁ h₂ h₃ c₁ c₂ c₃ ∈ distTriang (Karoubi C) :=
  triangleOfIdem_distinguished (Triangle.mk u v w) hT
    (Triangle.homMk _ _ p₁ p₂ p₃ c₁ c₂ c₃) (by ext <;> simp [h₁, h₂, h₃])

include h₁ h₂ h₃ c₁ c₂ c₃ in
/-- The complement of an idempotent endomorphism of a distinguished triangle whose first
morphism vanishes on the complement splits. -/
lemma exists_split_compl (hT : Triangle.mk u v w ∈ distTriang C) (hu : u ≫ (𝟙 _ - p₂) = 0) :
    ∃ (ρ : X₃ ⟶ X₂) (σ : X₁⟦(1 : ℤ)⟧ ⟶ X₃), (𝟙 _ - p₃) ≫ ρ = ρ ∧
      ρ ≫ v ≫ (𝟙 _ - p₃) + w ≫ (𝟙 _ - p₁)⟦(1 : ℤ)⟧' ≫ σ = 𝟙 _ - p₃ ∧
      v ≫ (𝟙 _ - p₃) ≫ ρ = 𝟙 _ - p₂ ∧
      σ ≫ w ≫ (𝟙 _ - p₁)⟦(1 : ℤ)⟧' = (𝟙 _ - p₁)⟦(1 : ℤ)⟧' := by
  have hc₁ : u ≫ (𝟙 _ - p₂) = (𝟙 _ - p₁) ≫ u := OctahedronAux.comp_compl c₁
  have hc₂ : v ≫ (𝟙 _ - p₃) = (𝟙 _ - p₂) ≫ v := OctahedronAux.comp_compl c₂
  have hc₃ : w ≫ (𝟙 _ - p₁)⟦(1 : ℤ)⟧' = (𝟙 _ - p₃) ≫ w := by
    rw [Functor.map_sub, Functor.map_id]; exact OctahedronAux.comp_compl c₃
  let Δ := triangleOfIdem' u v w (𝟙 _ - p₁) (𝟙 _ - p₂) (𝟙 _ - p₃)
    (OctahedronAux.compl_comp_compl h₁) (OctahedronAux.compl_comp_compl h₂)
    (OctahedronAux.compl_comp_compl h₃) hc₁ hc₂ hc₃
  have hΔ : Δ ∈ distTriang (Karoubi C) := triangleOfIdem'_distinguished _ _ _ _ _ _ _ _ _ _ _ _ hT
  have h0 : Δ.mor₁ = 0 := by
    ext
    change u ≫ (𝟙 _ - p₂) = 0
    exact hu
  obtain ⟨e₀, he₁, he₂⟩ := exists_iso_binaryBiproduct_of_distTriang _ (rot_of_distTriang _ hΔ)
    (by simp only [Triangle.rotate_mor₃, h0, Functor.map_zero, neg_zero])
  let e : Δ.obj₃ ≅ Δ.obj₂ ⊞ Δ.obj₁⟦(1 : ℤ)⟧ := e₀
  have he₁₀ : Δ.mor₂ ≫ e.hom = biprod.inl := he₁
  have he₁' : Δ.mor₂ = biprod.inl ≫ e.inv := by rw [← he₁₀]; simp
  have he₂' : Δ.mor₃ = e.hom ≫ biprod.snd := he₂
  let ρD : Δ.obj₃ ⟶ Δ.obj₂ := e.hom ≫ biprod.fst
  let σD : Δ.obj₁⟦(1 : ℤ)⟧ ⟶ Δ.obj₃ := biprod.inr ≫ e.inv
  refine ⟨ρD.f, σD.f, Karoubi.p_comp ρD, ?_, ?_, ?_⟩
  · have hD : ρD ≫ Δ.mor₂ + Δ.mor₃ ≫ σD = 𝟙 _ := by
      rw [he₁', he₂']
      simp only [ρD, σD, assoc]
      have : biprod.fst ≫ biprod.inl ≫ e.inv + biprod.snd ≫ biprod.inr ≫ e.inv = e.inv := by
        rw [← assoc, ← assoc, ← add_comp, biprod.total, id_comp]
      rw [← comp_add, this, e.hom_inv_id]
    simpa [Δ] using congrArg Karoubi.Hom.f hD
  · have hD : Δ.mor₂ ≫ ρD = 𝟙 _ := by
      rw [he₁']; simp [ρD]
    simpa [Δ] using congrArg Karoubi.Hom.f hD
  · have hD : σD ≫ Δ.mor₃ = 𝟙 _ := by
      rw [he₂']; simp [σD]
    exact congrArg Karoubi.Hom.f hD

end Raw

end CategoryTheory.Idempotents.Karoubi
