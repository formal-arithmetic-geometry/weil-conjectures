/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit

/-!
# `Ext` into the limit of a tower: the Milnor isomorphism

Let `C` be an abelian category with K-injective resolutions and exact countable products, and
`F : ℕᵒᵖ ⥤ C` a tower with limit `c` such that `1 - t` is an epimorphism on `∏ Fₙ` (e.g. a tower
of epimorphisms in a replete topos). The long exact `Ext`-sequence of the Milnor sequence
`0 ⟶ lim Fₙ ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ 0` gives the Milnor sequence
`0 ⟶ lim¹ Ext X Fₙ p ⟶ Ext X (lim Fₙ) (p + 1) ⟶ lim Ext X Fₙ (p + 1) ⟶ 0`. In particular, if
`1 - t` is surjective on `∏ Ext X Fₙ p` (that is, `lim¹ Ext X Fₙ p = 0`, e.g. when the tower
`Ext X Fₙ p` is Mittag-Leffler), then `Ext X (lim Fₙ) (p + 1) ≅ lim Ext X Fₙ (p + 1)`.

## Main statements

- `CategoryTheory.Abelian.Ext.bijective_of_isLimit_tower`: the map from `Ext X (lim Fₙ) (p + 1)`
  to the compatible families of `Ext X Fₙ (p + 1)` is bijective if `lim¹ Ext X Fₙ p = 0`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite DerivedCategory

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The compatible families `(yₙ)` of elements of `Ext X Fₙ q` along a tower `F`: the inverse
limit `lim Ext X Fₙ q`. -/
def TowerCompatible (X : C) (F : ℕᵒᵖ ⥤ C) (q : ℕ) : Type _ :=
  {y : ∀ n : ℕ, Ext X (F.obj (op n)) q //
    ∀ n : ℕ, (y (n + 1)).comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero q) = y n}

/-- The map `Ext X (lim Fₙ) q ⟶ lim Ext X Fₙ q`. -/
def toTowerCompatible (X : C) {F : ℕᵒᵖ ⥤ C} (c : Cone F) (q : ℕ) (x : Ext X c.pt q) :
    TowerCompatible X F q :=
  ⟨fun n ↦ x.comp (mk₀ (c.π.app (op n))) (add_zero q), fun n ↦ by
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, c.w]⟩

/-- **The Milnor isomorphism for `Ext`.** Let `F : ℕᵒᵖ ⥤ C` be a tower with limit `c` such that
`1 - t` is an epimorphism on products of the tower, where `t` has components
`∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`, and assume countable products are exact. If `1 - t` is surjective on
`∏ Ext X Fₙ p` (i.e. `lim¹ Ext X Fₙ p = 0`), then `Ext X (lim Fₙ) (p + 1) ⟶ lim Ext X Fₙ (p + 1)`
is bijective. -/
theorem bijective_toTowerCompatible [HasDerivedCategory C] [HasKInjectiveResolutions C]
    [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C] (X : C) {F : ℕᵒᵖ ⥤ C}
    (hF : ∀ ⦃P : Fan fun n : ℕ ↦ F.obj (op n)⦄ (_ : IsLimit P) (t : P.pt ⟶ P.pt),
      (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) →
        Epi (𝟙 P.pt - t))
    {c : Cone F} (hc : IsLimit c) (p : ℕ)
    (hML : ∀ y : ∀ n : ℕ, Ext X (F.obj (op n)) p, ∃ x : ∀ n : ℕ, Ext X (F.obj (op n)) p,
      ∀ n : ℕ, x n - (x (n + 1)).comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero p) =
        y n) :
    Function.Bijective (toTowerCompatible X c (p + 1)) := by
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let t : P.pt ⟶ P.pt := Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
    simp [t, P]
  let S : ShortComplex C :=
    ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)
  have hK := Fan.IsLimit.isLimitKernelForkOneSub hP t ht hc
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel hK
      mono_f := Fork.IsLimit.mono hK
      epi_g := hF hP t ht }
  have hf (n : ℕ) : S.f ≫ P.proj n = c.π.app (op n) :=
    Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n
  have hφ (m : ℕ) := bijective_comp_mk₀_proj X hP m
  have hneg {A B : C} (f : A ⟶ B) : mk₀ (-f) = -mk₀ f :=
    eq_neg_of_add_eq_zero_left (by rw [← mk₀_add, neg_add_cancel, mk₀_zero])
  -- the components of `W ∘ (1 - t)`
  have hg {m : ℕ} (W : Ext X P.pt m) (n : ℕ) :
      (W.comp (mk₀ S.g) (add_zero m)).comp (mk₀ (P.proj n)) (add_zero m) =
        W.comp (mk₀ (P.proj n)) (add_zero m) -
          (W.comp (mk₀ (P.proj (n + 1))) (add_zero m)).comp
            (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero m) := by
    have e : S.g ≫ P.proj n = P.proj n + -(P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) := by
      simp [S, ht, sub_eq_add_neg]
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, e, mk₀_add, hneg, ← mk₀_comp_mk₀, comp_add,
      comp_neg, ← comp_assoc_of_third_deg_zero, sub_eq_add_neg]
  have hfx {m : ℕ} (x : Ext X c.pt m) (n : ℕ) :
      (x.comp (mk₀ S.f) (add_zero m)).comp (mk₀ (P.proj n)) (add_zero m) =
        x.comp (mk₀ (c.π.app (op n))) (add_zero m) := by
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, hf]
  refine ⟨fun x x' hxx' ↦ ?_, fun y ↦ ?_⟩
  · -- injectivity: the kernel is the image of `lim¹`, which vanishes
    have hd (n : ℕ) : (x - x').comp (mk₀ (c.π.app (op n))) (add_zero _) = 0 := by
      rw [sub_comp, sub_eq_zero]
      exact congrFun (congrArg Subtype.val hxx') n
    have hdf : (x - x').comp (mk₀ S.f) (add_zero _) = 0 :=
      (hφ (p + 1)).1 (funext fun n ↦ by
        rw [Pi.zero_apply, zero_comp]
        exact (hfx _ n).trans (hd n))
    obtain ⟨z, hz⟩ := covariant_sequence_exact₁ X hS _ hdf rfl
    obtain ⟨w, hw⟩ := hML fun n ↦ z.comp (mk₀ (P.proj n)) (add_zero p)
    obtain ⟨W, hW⟩ := (hφ p).2 w
    have hWz : W.comp (mk₀ S.g) (add_zero p) = z := (hφ p).1 (funext fun n ↦ by
      have hW' (k : ℕ) : W.comp (mk₀ (P.proj k)) (add_zero p) = w k := congrFun hW k
      dsimp only
      rw [hg, hW', hW', hw])
    rw [← sub_eq_zero, ← hz, ← hWz, comp_assoc_of_second_deg_zero, hS.comp_extClass, comp_zero]
  · -- surjectivity: a compatible family lifts to `∏ Fₙ` and is killed by `1 - t`
    obtain ⟨Y, hY⟩ := (hφ (p + 1)).2 y.1
    have hY' (k : ℕ) : Y.comp (mk₀ (P.proj k)) (add_zero _) = y.1 k := congrFun hY k
    have hYg : Y.comp (mk₀ S.g) (add_zero _) = 0 := (hφ (p + 1)).1 (funext fun n ↦ by
      dsimp only
      rw [hg, hY', hY', y.2 n, sub_self, Pi.zero_apply, zero_comp])
    obtain ⟨x, hx⟩ := covariant_sequence_exact₂ X hS Y hYg
    refine ⟨x, Subtype.ext (funext fun n ↦ ?_)⟩
    change x.comp (mk₀ (c.π.app (op n))) (add_zero _) = y.1 n
    rw [← hfx, hx, hY']

end CategoryTheory.Abelian.Ext
