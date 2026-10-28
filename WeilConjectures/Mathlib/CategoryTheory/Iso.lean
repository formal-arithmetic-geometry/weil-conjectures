/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Iso

/-!
# Gluing commutative squares along isomorphisms

Two commutative squares `e₁ ≫ s = s₁ ≫ e₁'` and `e₂ ≫ s = s₂ ≫ e₂'` with isomorphisms as
horizontal sides and a common right side `s` glue to a commutative square
`(e₁ ≫ e₂⁻¹) ≫ s₂ = s₁ ≫ (e₁' ≫ e₂'⁻¹)`.

We also record two-out-of-three style criteria for a morphism in a commutative diagram of
isomorphisms to be an isomorphism (`CategoryTheory.isIso_of_comp_eq_comp_comp`,
`CategoryTheory.isIso_map_of_map_comp_eq`).
-/

@[expose] public section

namespace CategoryTheory.Iso

/-- Two commutative squares with a common right side `s : D ⟶ D'`, glued along the isomorphisms
to `D` and `D'`:
```
A₁ --e₁--> D <--e₂-- A₂
|s₁        |s        |s₂
B₁ --e₁'-> D' <-e₂'- B₂
```
-/
lemma comp_inv_comp_eq_of_comm {𝒜 : Type*} [Category* 𝒜]
    {A₁ A₂ D B₁ B₂ D' : 𝒜} (e₁ : A₁ ≅ D) (e₂ : A₂ ≅ D) (e₁' : B₁ ≅ D') (e₂' : B₂ ≅ D')
    (s₁ : A₁ ⟶ B₁) (s₂ : A₂ ⟶ B₂) (s : D ⟶ D') (h₁ : e₁.hom ≫ s = s₁ ≫ e₁'.hom)
    (h₂ : e₂.hom ≫ s = s₂ ≫ e₂'.hom) : e₁.hom ≫ e₂.inv ≫ s₂ = s₁ ≫ e₁'.hom ≫ e₂'.inv := by
  have : e₂.inv ≫ s₂ = s ≫ e₂'.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% h₂, Iso.hom_inv_id, Category.comp_id]
  rw [this, reassoc_of% h₁]

end CategoryTheory.Iso

namespace CategoryTheory

/-- In a commutative square
```
A --f₁--> B
|g₁       |f₂
v         v
D --g₂--> E --g₃--> F
```
with `f₁ ≫ f₂ = g₁ ≫ g₂ ≫ g₃` and `f₁`, `f₂`, `g₁`, `g₃` isomorphisms, `g₂` is an isomorphism. -/
lemma isIso_of_comp_eq_comp_comp {C : Type*} [Category* C] {A B D E F : C} {f₁ : A ⟶ B}
    {f₂ : B ⟶ F} {g₁ : A ⟶ D} {g₂ : D ⟶ E} {g₃ : E ⟶ F} (h : f₁ ≫ f₂ = g₁ ≫ g₂ ≫ g₃) [IsIso f₁]
    (hf₂ : IsIso f₂) [IsIso g₁] [IsIso g₃] : IsIso g₂ := by
  have : IsIso (g₁ ≫ g₂ ≫ g₃) := h ▸ inferInstance
  have := IsIso.of_isIso_comp_left g₁ (g₂ ≫ g₃)
  exact IsIso.of_isIso_comp_right g₂ g₃

/-- If a commutative square
```
P --a--> Q --b--> R --c--> S
|d                         ‖
v                          ‖
T ----------e------------> S
```
satisfies `a ≫ b ≫ c = d ≫ e` with `b`, `c`, `e`, `F d` isomorphisms, then `F a` is an
isomorphism. -/
lemma isIso_map_of_map_comp_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P Q R S T : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : P ⟶ T} {e : T ⟶ S}
    (h : a ≫ b ≫ c = d ≫ e) [IsIso b] (hc : IsIso c) (hd : IsIso (F.map d)) [IsIso e] :
    IsIso (F.map a) := by
  have h' := congr(F.map $h)
  simp only [Functor.map_comp] at h'
  have : IsIso (F.map a ≫ F.map b ≫ F.map c) := by rw [h']; infer_instance
  exact IsIso.of_isIso_comp_right (F.map a) (F.map b ≫ F.map c)

end CategoryTheory
