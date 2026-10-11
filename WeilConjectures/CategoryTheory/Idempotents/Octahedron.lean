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

## Main statements

- `CategoryTheory.Idempotents.Karoubi.isTriangulated`: the Karoubi envelope of a triangulated
  category is triangulated.
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

lemma m₁_corrY (hg₂ : p₂ ≫ g = g)
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

lemma corrX_m₃ (hv₁₃ : v₁₃ ≫ s₁₃ = p₃ ≫ v₁₃)
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
    ⟨u ≫ p₂, comm_of_comp_eq u h₂ c₁⟩
    ⟨v ≫ p₃, comm_of_comp_eq v h₃ c₂⟩
    ⟨w ≫ p₁⟦(1 : ℤ)⟧', comm_of_comp_eq w
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

lemma exists_idempotent_raw {X₁ X₂ X₃ : C} (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈ distTriang C) (a : X₁ ⟶ X₁) (b : X₂ ⟶ X₂) (ha : a ≫ a = a)
    (hb : b ≫ b = b) (hab : u ≫ b = a ≫ u) :
    ∃ (c : X₃ ⟶ X₃), c ≫ c = c ∧ v ≫ c = b ≫ v ∧ w ≫ a⟦(1 : ℤ)⟧' = c ≫ w :=
  Pretriangulated.exists_idempotent_of_distTriang _ hT a b ha hb hab

open OctahedronAux in
/-- Blueprint `lem-weil-karoubi-envelope-triangulated`, octahedral axiom: the Karoubi envelope of
a triangulated category is triangulated. -/
instance isTriangulated [IsTriangulated C] : IsTriangulated (Karoubi C) := by
  apply IsTriangulated.mk'
  intro P₁ P₂ P₃ U G
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := Pretriangulated.distinguished_cocone_triangle U.f
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := Pretriangulated.distinguished_cocone_triangle G.f
  obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (U.f ≫ G.f)
  have hu₁ : P₁.p ≫ U.f = U.f := Karoubi.p_comp U
  have hu₂ : U.f ≫ P₂.p = U.f := Karoubi.comp_p U
  have hg₂ : P₂.p ≫ G.f = G.f := Karoubi.p_comp G
  have hg₃ : G.f ≫ P₃.p = G.f := Karoubi.comp_p G
  have cu : U.f ≫ P₂.p = P₁.p ≫ U.f := by rw [hu₁, hu₂]
  have cg : G.f ≫ P₃.p = P₂.p ≫ G.f := by rw [hg₂, hg₃]
  have cug : (U.f ≫ G.f) ≫ P₃.p = P₁.p ≫ (U.f ≫ G.f) := by rw [assoc, hg₃, reassoc_of% hu₁]
  obtain ⟨s₁₂, hs₁₂, cv₁₂, cw₁₂⟩ :=
    exists_idempotent_raw _ _ _ h₁₂ P₁.p P₂.p P₁.idem P₂.idem cu
  obtain ⟨s₂₃, hs₂₃, cv₂₃, cw₂₃⟩ :=
    exists_idempotent_raw _ _ _ h₂₃ P₂.p P₃.p P₂.idem P₃.idem cg
  obtain ⟨s₁₃, hs₁₃, cv₁₃, cw₁₃⟩ :=
    exists_idempotent_raw _ _ _ h₁₃ P₁.p P₃.p P₁.idem P₃.idem cug
  let O := Triangulated.someOctahedron rfl h₁₂ h₂₃ h₁₃
  have hmm : O.m₁ ≫ O.m₃ = 0 := comp_distTriang_mor_zero₁₂ _ O.mem
  have hvw₁₃ : v₁₃ ≫ w₁₃ = 0 := comp_distTriang_mor_zero₂₃ _ h₁₃
  -- splittings of the complementary triangles
  obtain ⟨ρ₁₂, σ₁₂, -, S₁₂, -, T₁₂⟩ := exists_split_compl U.f v₁₂ w₁₂ P₁.p P₂.p s₁₂ P₁.idem
    P₂.idem hs₁₂ cu cv₁₂ cw₁₂ h₁₂ (by rw [comp_sub, hu₂, comp_id, sub_self])
  obtain ⟨ρ₁₃, σ₁₃, -, S₁₃, -, -⟩ := exists_split_compl (U.f ≫ G.f) v₁₃ w₁₃ P₁.p P₃.p s₁₃
    P₁.idem P₃.idem hs₁₃ cug cv₁₃ cw₁₃ h₁₃ (by rw [comp_sub, comp_id, assoc, hg₃, sub_self])
  obtain ⟨ρ₂₃, σ₂₃, hρ₂₃, S₂₃, T₂₃, -⟩ := exists_split_compl G.f v₂₃ w₂₃ P₂.p P₃.p s₂₃
    P₂.idem P₃.idem hs₂₃ cg cv₂₃ cw₂₃ h₂₃ (by rw [comp_sub, hg₃, comp_id, sub_self])
  simp only [Functor.map_sub, Functor.map_id] at S₁₂ T₁₂ S₁₃ S₂₃
  have hq₁ : P₁.p⟦(1 : ℤ)⟧' ≫ P₁.p⟦(1 : ℤ)⟧' = P₁.p⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp, P₁.idem]
  have hU₁ : U.f⟦(1 : ℤ)⟧' ≫ (𝟙 _ - P₂.p⟦(1 : ℤ)⟧') = 0 := by
    rw [comp_sub, comp_id, ← Functor.map_comp, hu₂, sub_self]
  have i₁ := m₁_corrX hs₁₃ hs₂₃ hq₁ cw₁₂.symm cv₁₃ cv₂₃ O.comm₂ O.comm₃ hmm S₁₃ T₂₃
  have i₂ := corrX_m₃ cv₁₃ cv₂₃ O.comm₃ O.comm₄ hU₁ hρ₂₃ S₂₃
  have r₁ := m₁_corrY hg₂ cv₁₂ cw₁₃.symm O.comm₁ O.comm₂ S₁₂
  have r₂ := corrY_m₃ hs₁₃ P₃.idem hq₁ cv₁₃ cw₁₃.symm cv₂₃ O.comm₂ O.comm₃ hmm S₁₃ T₁₂
  have xy := corrX_corrY (m₃ := O.m₃) (s₂₃ := s₂₃) (ρ₂₃ := ρ₂₃) (σ₁₂ := σ₁₂) (m₁ := O.m₁)
    hs₁₃ cw₁₃.symm hvw₁₃
  have hsx := s_corrX (m₃ := O.m₃) (s₂₃ := s₂₃) (ρ₂₃ := ρ₂₃) (v₁₃ := v₁₃) hs₁₃
  have hxs := corrX_s (m₃ := O.m₃) (s₂₃ := s₂₃) (ρ₂₃ := ρ₂₃) (v₁₃ := v₁₃) hs₁₃
  have hys := corrY_s (w₁₃ := w₁₃) (σ₁₂ := σ₁₂) (m₁ := O.m₁) hs₁₃
  have hsy := s_corrY (w₁₃ := w₁₃) (σ₁₂ := σ₁₂) (m₁ := O.m₁) hs₁₃
  -- the triangles of the envelope
  have hΔ₁₂ := triangleOfIdem'_distinguished U.f v₁₂ w₁₂ P₁.p P₂.p s₁₂ P₁.idem P₂.idem hs₁₂
    cu cv₁₂ cw₁₂ h₁₂
  have hΔ₂₃ := triangleOfIdem'_distinguished G.f v₂₃ w₂₃ P₂.p P₃.p s₂₃ P₂.idem P₃.idem hs₂₃
    cg cv₂₃ cw₂₃ h₂₃
  have hΔ₁₃ := triangleOfIdem'_distinguished (U.f ≫ G.f) v₁₃ w₁₃ P₁.p P₃.p s₁₃ P₁.idem P₃.idem
    hs₁₃ cug cv₁₃ cw₁₃ h₁₃
  have hΔ₁₃' : Triangle.mk ((triangleOfIdem' U.f v₁₂ w₁₂ P₁.p P₂.p s₁₂ P₁.idem P₂.idem hs₁₂
      cu cv₁₂ cw₁₂).mor₁ ≫ (triangleOfIdem' G.f v₂₃ w₂₃ P₂.p P₃.p s₂₃ P₂.idem P₃.idem hs₂₃
      cg cv₂₃ cw₂₃).mor₁) (triangleOfIdem' (U.f ≫ G.f) v₁₃ w₁₃ P₁.p P₃.p s₁₃ P₁.idem P₃.idem
      hs₁₃ cug cv₁₃ cw₁₃).mor₂ (triangleOfIdem' (U.f ≫ G.f) v₁₃ w₁₃ P₁.p P₃.p s₁₃ P₁.idem
      P₃.idem hs₁₃ cug cv₁₃ cw₁₃).mor₃ ∈ distTriang (Karoubi C) := by
    have e : (triangleOfIdem' U.f v₁₂ w₁₂ P₁.p P₂.p s₁₂ P₁.idem P₂.idem hs₁₂ cu cv₁₂ cw₁₂).mor₁ ≫
        (triangleOfIdem' G.f v₂₃ w₂₃ P₂.p P₃.p s₂₃ P₂.idem P₃.idem hs₂₃ cg cv₂₃ cw₂₃).mor₁ =
        (triangleOfIdem' (U.f ≫ G.f) v₁₃ w₁₃ P₁.p P₃.p s₁₃ P₁.idem P₃.idem hs₁₃ cug cv₁₃
          cw₁₃).mor₁ := by
      ext
      simp [hu₂]
    rw [e]
    exact hΔ₁₃
  refine ⟨P₁, P₂, P₃, ⟨Z₁₂, s₁₂, hs₁₂⟩, ⟨Z₂₃, s₂₃, hs₂₃⟩, ⟨Z₁₃, s₁₃, hs₁₃⟩, _, _,
    Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_, _, _, hΔ₁₂, _, _, hΔ₂₃, _, _, hΔ₁₃', ⟨?_⟩⟩
  · ext; simp [hu₂]
  · ext; simp [hg₃]
  have hM₁ : s₁₂ ≫ (s₁₂ ≫ O.m₁ ≫ s₁₃) ≫ s₁₃ = s₁₂ ≫ O.m₁ ≫ s₁₃ := by
    simp only [assoc, hs₁₃, reassoc_of% hs₁₂]
  have hM₃ : s₁₃ ≫ (s₁₃ ≫ O.m₃ ≫ s₂₃) ≫ s₂₃ = s₁₃ ≫ O.m₃ ≫ s₂₃ := by
    simp only [assoc, hs₂₃, reassoc_of% hs₁₃]
  exact
    { m₁ := ⟨s₁₂ ≫ O.m₁ ≫ s₁₃, hM₁⟩
      m₃ := ⟨s₁₃ ≫ O.m₃ ≫ s₂₃, hM₃⟩
      comm₁ := by
        ext
        change (v₁₂ ≫ s₁₂) ≫ (s₁₂ ≫ O.m₁ ≫ s₁₃) = (G.f ≫ P₃.p) ≫ (v₁₃ ≫ s₁₃)
        rw [assoc, reassoc_of% hs₁₂, reassoc_of% cv₁₂, reassoc_of% O.comm₁, reassoc_of% hg₂,
          assoc, ← reassoc_of% cv₁₃, hs₁₃]
      comm₂ := by
        ext
        change (s₁₂ ≫ O.m₁ ≫ s₁₃) ≫ (w₁₃ ≫ P₁.p⟦(1 : ℤ)⟧') = w₁₂ ≫ P₁.p⟦(1 : ℤ)⟧'
        simp only [assoc]
        rw [← reassoc_of% cw₁₃, reassoc_of% O.comm₂, hq₁, ← reassoc_of% cw₁₂, hq₁]
      comm₃ := by
        ext
        change (v₁₃ ≫ s₁₃) ≫ (s₁₃ ≫ O.m₃ ≫ s₂₃) = v₂₃ ≫ s₂₃
        simp only [assoc]
        rw [reassoc_of% hs₁₃, reassoc_of% cv₁₃, reassoc_of% O.comm₃, cv₂₃, reassoc_of% P₃.idem]
      comm₄ := by
        ext
        change (w₁₃ ≫ P₁.p⟦(1 : ℤ)⟧') ≫ (U.f ≫ P₂.p)⟦(1 : ℤ)⟧' =
          (s₁₃ ≫ O.m₃ ≫ s₂₃) ≫ (w₂₃ ≫ P₂.p⟦(1 : ℤ)⟧')
        have hq₂ : P₂.p⟦(1 : ℤ)⟧' ≫ P₂.p⟦(1 : ℤ)⟧' = P₂.p⟦(1 : ℤ)⟧' := by
          rw [← Functor.map_comp, P₂.idem]
        simp only [assoc, Functor.map_comp]
        rw [← reassoc_of% cw₂₃, ← reassoc_of% O.comm₄, ← reassoc_of% cw₁₃, hq₂]
      mem := by
        refine (Karoubi.mem_distTriang_iff _).2 ⟨_, O.mem, ⟨
          { i := Triangle.homMk _ _
              (⟨s₁₂, by simp [hs₁₂]⟩ : (⟨Z₁₂, s₁₂, hs₁₂⟩ : Karoubi C) ⟶ (toKaroubi C).obj Z₁₂)
              (⟨s₁₃ + corrX s₁₃ O.m₃ s₂₃ ρ₂₃ v₁₃, by
                change s₁₃ ≫ (s₁₃ + corrX s₁₃ O.m₃ s₂₃ ρ₂₃ v₁₃) ≫ 𝟙 Z₁₃ = _
                rw [Category.comp_id, comp_add, hs₁₃, hsx]⟩ :
                (⟨Z₁₃, s₁₃, hs₁₃⟩ : Karoubi C) ⟶ (toKaroubi C).obj Z₁₃)
              (⟨s₂₃, by simp [hs₂₃]⟩ : (⟨Z₂₃, s₂₃, hs₂₃⟩ : Karoubi C) ⟶ (toKaroubi C).obj Z₂₃)
              ?_ ?_ ?_
            r := Triangle.homMk _ _
              (⟨s₁₂, by simp [hs₁₂]⟩ : (toKaroubi C).obj Z₁₂ ⟶ (⟨Z₁₂, s₁₂, hs₁₂⟩ : Karoubi C))
              (⟨s₁₃ + corrY s₁₃ w₁₃ σ₁₂ O.m₁, by
                change 𝟙 Z₁₃ ≫ (s₁₃ + corrY s₁₃ w₁₃ σ₁₂ O.m₁) ≫ s₁₃ = _
                rw [Category.id_comp, add_comp, hs₁₃, hys]⟩ :
                (toKaroubi C).obj Z₁₃ ⟶ (⟨Z₁₃, s₁₃, hs₁₃⟩ : Karoubi C))
              (⟨s₂₃, by simp [hs₂₃]⟩ : (toKaroubi C).obj Z₂₃ ⟶ (⟨Z₂₃, s₂₃, hs₂₃⟩ : Karoubi C))
              ?_ ?_ ?_
            retract := ?_ }⟩⟩
        · ext
          change (s₁₂ ≫ O.m₁ ≫ s₁₃) ≫ (s₁₃ + corrX s₁₃ O.m₃ s₂₃ ρ₂₃ v₁₃) = s₁₂ ≫ O.m₁
          rw [comp_add]
          simp only [assoc, hs₁₃, i₁]
          rw [← comp_add, ← comp_add, add_sub_cancel, comp_id]
        · ext
          change (s₁₃ ≫ O.m₃ ≫ s₂₃) ≫ s₂₃ = (s₁₃ + corrX s₁₃ O.m₃ s₂₃ ρ₂₃ v₁₃) ≫ O.m₃
          simp only [assoc, hs₂₃, add_comp, i₂, comp_sub, comp_id]
          abel
        · ext
          change ((w₂₃ ≫ P₂.p⟦(1 : ℤ)⟧') ≫ (v₁₂ ≫ s₁₂)⟦(1 : ℤ)⟧') ≫ s₁₂⟦(1 : ℤ)⟧' =
            s₂₃ ≫ (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ≫ 𝟙 _
          have k : P₂.p⟦(1 : ℤ)⟧' ≫ (v₁₂ ≫ s₁₂)⟦(1 : ℤ)⟧' ≫ s₁₂⟦(1 : ℤ)⟧' =
              P₂.p⟦(1 : ℤ)⟧' ≫ v₁₂⟦(1 : ℤ)⟧' := by
            rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, assoc, hs₁₂, cv₁₂,
              reassoc_of% P₂.idem]
          simp only [assoc]
          rw [k, comp_id, ← reassoc_of% cw₂₃]
        · ext
          change O.m₁ ≫ (s₁₃ + corrY s₁₃ w₁₃ σ₁₂ O.m₁) = s₁₂ ≫ s₁₂ ≫ O.m₁ ≫ s₁₃
          rw [comp_add, r₁, reassoc_of% hs₁₂, sub_comp, id_comp]
          abel
        · ext
          change O.m₃ ≫ s₂₃ = (s₁₃ + corrY s₁₃ w₁₃ σ₁₂ O.m₁) ≫ s₁₃ ≫ O.m₃ ≫ s₂₃
          rw [add_comp, reassoc_of% hs₁₃, r₂, ← add_comp, add_sub_cancel, id_comp]
        · ext
          change ((w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ≫ 𝟙 _) ≫ s₁₂⟦(1 : ℤ)⟧' =
            s₂₃ ≫ (w₂₃ ≫ P₂.p⟦(1 : ℤ)⟧') ≫ (v₁₂ ≫ s₁₂)⟦(1 : ℤ)⟧'
          have k2 : P₂.p⟦(1 : ℤ)⟧' ≫ P₂.p⟦(1 : ℤ)⟧' ≫ (v₁₂ ≫ s₁₂)⟦(1 : ℤ)⟧' =
              (v₁₂ ≫ s₁₂)⟦(1 : ℤ)⟧' := by
            rw [← Functor.map_comp, ← Functor.map_comp, reassoc_of% P₂.idem, ← reassoc_of% cv₁₂,
              hs₁₂]
          simp only [assoc, comp_id]
          rw [← reassoc_of% cw₂₃, k2, Functor.map_comp]
        · ext
          · exact hs₁₂
          · change (s₁₃ + corrX s₁₃ O.m₃ s₂₃ ρ₂₃ v₁₃) ≫ (s₁₃ + corrY s₁₃ w₁₃ σ₁₂ O.m₁) = s₁₃
            rw [add_comp, comp_add, comp_add, hs₁₃, hsy, hxs, xy]
            simp
          · exact hs₂₃
        }

end CategoryTheory.Idempotents.Karoubi
