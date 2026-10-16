/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Existence of derived limits and the Milnor exact sequence

Let `C` be a pretriangulated category and `F : ℕᵒᵖ ⥤ C` a tower.

* If the product `∏ₙ Fₙ` exists, then `F` has a derived limit
  (`CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_cone`): complete `1 - t` to a
  distinguished triangle. Two derived limits are isomorphic, compatibly with the legs, but not
  canonically (`CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso`).
* For a Roos triangle `L ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ──δ──▶ L⟦1⟧` and an object `X`, the long exact
  `Hom(X, -)` sequence gives the *Milnor exact sequence*
  `0 ⟶ lim¹ₙ Hom(X, Fₙ) ⟶ Hom(X, L⟦1⟧) ⟶ limₙ Hom(X, Fₙ⟦1⟧) ⟶ 0`, where `lim¹` of the tower of
  groups `Hom(X, Fₙ)` is the cokernel of `1 - t` on `∏ₙ Hom(X, Fₙ) = Hom(X, ∏ₙ Fₙ)`. It is stated
  elementwise:
  - `CategoryTheory.Pretriangulated.milnor_surjective`: every compatible family
    `X ⟶ Fₙ⟦1⟧` comes from a map `X ⟶ L⟦1⟧`;
  - `CategoryTheory.Pretriangulated.milnor_exact_middle`: a map `X ⟶ L⟦1⟧` whose components all
    vanish factors through `δ`;
  - `CategoryTheory.Pretriangulated.milnor_comp_δ_eq_zero_iff`: `x ≫ δ = 0` exactly when `x` is
    in the image of `1 - t`.

Taking `X` to be a shift of the unit section `Λ_U` of an object `U` of a site gives the sequence
`0 ⟶ lim¹ Hⁱ⁻¹(U, Mₙ) ⟶ Hⁱ(U, R lim Mₙ) ⟶ lim Hⁱ(U, Mₙ) ⟶ 0`.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Blueprint `lem-weil-derived-limit-existence`** (assertion 1, existence). A tower in a
pretriangulated category whose product exists has a derived limit: the first term of a
distinguished triangle completing `1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ`. Uniqueness up to non-canonical
isomorphism is `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso`. -/
lemma IsHomotopyLimit.exists_cone (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)] :
    ∃ c : Cone F, IsHomotopyLimit c := by
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  obtain ⟨X, f, δ, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  have hf : f ≫ (𝟙 P.pt - towerShift hP) = 0 := comp_distTriang_mor_zero₁₂ _ hT
  let c : Cone F :=
    { pt := X
      π := NatTrans.ofOpSequence (fun n ↦ f ≫ P.proj n) fun n ↦ by
        have := hf =≫ P.proj n
        simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
          Category.assoc, towerShift, Fan.IsLimit.fac, zero_comp, sub_eq_zero] at this
        simpa using this }
  refine ⟨c, P, hP, δ, ?_⟩
  have : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) = f :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [c]
  rw [this]
  exact hT

section Milnor

variable {F : ℕᵒᵖ ⥤ C} {c : Cone F} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)
  {δ : P.pt ⟶ c.pt⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) (𝟙 P.pt - towerShift hP) δ ∈
    distTriang C)

/-- The shifted product `(∏ₙ Fₙ)⟦1⟧` is a product of the `Fₙ⟦1⟧`. -/
noncomputable def isLimitShiftFan :
    IsLimit (Fan.mk (P.pt⟦(1 : ℤ)⟧) fun n ↦ (P.proj n)⟦(1 : ℤ)⟧') :=
  isLimitFanMkObjOfIsLimit (shiftFunctor C (1 : ℤ)) _ _ hP

include hT

/-- **Blueprint `prop-weil-pbc-roos-triangle`** (Milnor sequence, surjectivity onto `lim`). For a
Roos triangle `L ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ──δ──▶ L⟦1⟧`, every family of maps `yₙ : X ⟶ Fₙ⟦1⟧`
compatible with the transitions comes from a map `X ⟶ L⟦1⟧`. -/
lemma milnor_surjective {X : C} (y : ∀ n : ℕ, X ⟶ (F.obj (op n))⟦(1 : ℤ)⟧)
    (hy : ∀ n, y (n + 1) ≫ (F.map (homOfLE n.le_succ).op)⟦(1 : ℤ)⟧' = y n) :
    ∃ g : X ⟶ c.pt⟦(1 : ℤ)⟧, ∀ n, g ≫ (c.π.app (op n))⟦(1 : ℤ)⟧' = y n := by
  have hP₁ := isLimitShiftFan hP
  let f : X ⟶ P.pt⟦(1 : ℤ)⟧ := Fan.IsLimit.lift hP₁ y
  have hf (n : ℕ) : f ≫ (P.proj n)⟦(1 : ℤ)⟧' = y n := Fan.IsLimit.fac hP₁ y n
  have hf₀ : f ≫ (𝟙 P.pt - towerShift hP)⟦(1 : ℤ)⟧' = 0 := Fan.IsLimit.hom_ext hP₁ _ _ fun n ↦ by
    simp only [fan_mk_proj, zero_comp, Category.assoc]
    rw [← Functor.map_comp, Preadditive.sub_comp, Category.id_comp, towerShift_proj,
      Functor.map_sub, Preadditive.comp_sub, Functor.map_comp, hf, reassoc_of% hf, hy, sub_self]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ (rot_of_distTriang _ hT) f hf₀
  refine ⟨-g, fun n ↦ ?_⟩
  have := hg =≫ (P.proj n)⟦(1 : ℤ)⟧'
  simp only [Triangle.rotate_mor₃, Triangle.mk_mor₁,
    Preadditive.comp_neg, Category.assoc, Preadditive.neg_comp, hf] at this
  rw [← Functor.map_comp, Fan.IsLimit.fac] at this
  rw [Preadditive.neg_comp, this]

/-- **Blueprint `prop-weil-pbc-roos-triangle`** (Milnor sequence, exactness in the middle). A map
`X ⟶ L⟦1⟧` whose composites with all the shifted legs `L⟦1⟧ ⟶ Fₙ⟦1⟧` vanish factors through
`δ : ∏ₙ Fₙ ⟶ L⟦1⟧`, and conversely. -/
lemma milnor_exact_middle {X : C} (g : X ⟶ c.pt⟦(1 : ℤ)⟧) :
    (∀ n, g ≫ (c.π.app (op n))⟦(1 : ℤ)⟧' = 0) ↔ ∃ x : X ⟶ P.pt, g = x ≫ δ := by
  have hP₁ := isLimitShiftFan hP
  constructor
  · intro hg
    refine Triangle.coyoneda_exact₁ _ hT g (Fan.IsLimit.hom_ext hP₁ _ _ fun n ↦ ?_)
    simp only [Triangle.mk_mor₁, fan_mk_proj, Category.assoc, zero_comp,
      ← Functor.map_comp, Fan.IsLimit.fac, hg]
  · rintro ⟨x, rfl⟩ n
    have h₃ := comp_distTriang_mor_zero₃₁ _ hT
    simp only [Triangle.mk_mor₃, Triangle.mk_mor₁] at h₃
    rw [Category.assoc, ← Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n, Functor.map_comp,
      reassoc_of% h₃, zero_comp, comp_zero]

/-- **Blueprint `prop-weil-pbc-roos-triangle`** (Milnor sequence, the `lim¹` term). A map
`x : X ⟶ ∏ₙ Fₙ` is killed by `δ` exactly when it lies in the image of `1 - t`: the kernel of
`Hom(X, ∏ Fₙ) ⟶ Hom(X, L⟦1⟧)` is the image of `1 - t`, so its image is `lim¹ₙ Hom(X, Fₙ)`. -/
lemma milnor_comp_δ_eq_zero_iff {X : C} (x : X ⟶ P.pt) :
    x ≫ δ = 0 ↔ ∃ z : X ⟶ P.pt, x = z ≫ (𝟙 P.pt - towerShift hP) := by
  constructor
  · exact Triangle.coyoneda_exact₃ _ hT x
  · rintro ⟨z, rfl⟩
    rw [Category.assoc]
    have := comp_distTriang_mor_zero₂₃ _ hT
    simp only [Triangle.mk_mor₂, Triangle.mk_mor₃] at this
    rw [this, comp_zero]

end Milnor

end CategoryTheory.Pretriangulated
