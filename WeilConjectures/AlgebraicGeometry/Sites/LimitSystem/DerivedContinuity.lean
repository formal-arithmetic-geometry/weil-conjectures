/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.Derived

/-!
# Continuity of hypercohomology of bounded below complexes at cofiltered limits

Let `(Dᵢ)` be a cofiltered system of schemes over `S`, with limit `X`, and let `K` be a complex
of abelian étale sheaves on `S`. Continuity of `Hⁿ(-, K)` along the system
(`AlgebraicGeometry.Etale.IsHyperHContinuousAt`) means that every class on `X` comes from some
`Dᵢ`, and that a class on `Dᵢ` which vanishes on `X` already vanishes on some `Dⱼ`, `j ⟶ i`.

This property is stable under shifts and isomorphisms, and satisfies the five lemma along the
long exact cohomology sequences of distinguished triangles
(`AlgebraicGeometry.Etale.isHyperHContinuousAt_of_triangle`). By induction on the length of a
bounded complex, along the truncation triangles, it reduces to the case of a single sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {S : Scheme.{u}}

section Postcomp

/-- Composition with the pullback of a morphism `β : K ⟶ L[m]` of complexes on `S`, as a map
`Hⁿ(T, K|_T) ⟶ Hⁿ⁺ᵐ(T, L|_T)`. -/
noncomputable def overPostcomp (T : Over S)
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} {m n n' : ℤ}
    (β : ShiftedHom K L m) (h : m + n = n') :
    hyperH ((overPullback T).obj K) n →+ hyperH ((overPullback T).obj L) n' where
  toFun x := x.comp (β.map (overPullback T)) h
  map_zero' := ShiftedHom.zero_comp _ _ _
  map_add' _ _ := ShiftedHom.add_comp _ _ _ _

lemma overRestrict_overPostcomp {T T' : Over S} (g : T' ⟶ T)
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} {m n n' : ℤ}
    (β : ShiftedHom K L m) (h : m + n = n') (x : hyperH ((overPullback T).obj K) n) :
    overRestrict g L n' (overPostcomp T β h x) = overPostcomp T' β h (overRestrict g K n x) :=
  overRestrict_comp_map g x β h

lemma overPostcomp_overPostcomp (T : Over S)
    {K L M : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    {m m' n n' n'' : ℤ} (β : ShiftedHom K L m) (γ : ShiftedHom L M m') (h : m + n = n')
    (h' : m' + n' = n'') (x : hyperH ((overPullback T).obj K) n) :
    overPostcomp T γ h' (overPostcomp T β h x) =
      overPostcomp T (β.comp γ rfl) (by omega) x := by
  simp only [overPostcomp, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [ShiftedHom.map_comp, ShiftedHom.comp_assoc _ _ _ h h' (by omega)]

lemma overPostcomp_mk₀_id (T : Over S)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) {n n' : ℤ}
    (h : 0 + n = n') (x : hyperH ((overPullback T).obj K) n) :
    overPostcomp T (ShiftedHom.mk₀ 0 rfl (𝟙 K)) h x = h ▸ x := by
  subst h
  simp [overPostcomp, ShiftedHom.map_mk₀]

end Postcomp

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S) (c : Cone D)

/-- Continuity of `Hⁿ(-, K)` along the cofiltered system `D` with cone `c`: every class on
the cone point comes from some `Dᵢ`, and a class on `Dᵢ` vanishing on the cone point vanishes
on some `Dⱼ`. -/
def IsHyperHContinuousAt (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) : Prop :=
  (∀ x : hyperH ((overPullback c.pt).obj K) n,
    ∃ (i : I) (y : hyperH ((overPullback (D.obj i)).obj K) n), overRestrict (c.π.app i) K n y = x) ∧
  ∀ (i : I) (y : hyperH ((overPullback (D.obj i)).obj K) n), overRestrict (c.π.app i) K n y = 0 →
    ∃ (j : I) (g : j ⟶ i), overRestrict (D.map g) K n y = 0

variable {D c}

lemma isHyperHContinuousAt_of_subsingleton
    {K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} {n : ℤ}
    (h : ∀ T : Over S, Subsingleton (hyperH ((overPullback T).obj K) n)) :
    IsHyperHContinuousAt D c K n := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  refine ⟨fun x ↦ ⟨i, 0, Subsingleton.elim _ _⟩, fun i y _ ↦ ⟨i, 𝟙 i, Subsingleton.elim _ _⟩⟩

/-- Continuity is transported along invertible morphisms `β : K ⟶ L[m]`. -/
lemma IsHyperHContinuousAt.of_shiftedHom
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} {m n n' : ℤ}
    (β : ShiftedHom K L m) (γ : ShiftedHom L K (-m))
    (hβγ : β.comp γ (neg_add_cancel m) = ShiftedHom.mk₀ 0 rfl (𝟙 K))
    (hγβ : γ.comp β (add_neg_cancel m) = ShiftedHom.mk₀ 0 rfl (𝟙 L)) (h : m + n = n')
    (hK : IsHyperHContinuousAt D c K n) : IsHyperHContinuousAt D c L n' := by
  have h' : -m + n' = n := by omega
  have hβγ' (T : Over S) (x : hyperH ((overPullback T).obj K) n) :
      overPostcomp T γ h' (overPostcomp T β h x) = x := by
    rw [overPostcomp_overPostcomp, hβγ, overPostcomp_mk₀_id]
  have hγβ' (T : Over S) (x : hyperH ((overPullback T).obj L) n') :
      overPostcomp T β h (overPostcomp T γ h' x) = x := by
    rw [overPostcomp_overPostcomp, hγβ, overPostcomp_mk₀_id]
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨i, y, hy⟩ := hK.1 (overPostcomp _ γ h' x)
    exact ⟨i, overPostcomp _ β h y, by rw [overRestrict_overPostcomp, hy, hγβ']⟩
  · obtain ⟨j, g, hg⟩ := hK.2 i (overPostcomp _ γ h' y)
      (by rw [← overRestrict_overPostcomp, hy, map_zero])
    refine ⟨j, g, ?_⟩
    rw [← hγβ' _ y, overRestrict_overPostcomp, overRestrict_overPostcomp, hg, map_zero]

lemma IsHyperHContinuousAt.of_iso
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} (e : K ≅ L)
    {n : ℤ} (hK : IsHyperHContinuousAt D c K n) : IsHyperHContinuousAt D c L n :=
  hK.of_shiftedHom (m := 0) (ShiftedHom.mk₀ 0 rfl e.hom) (ShiftedHom.mk₀ (-0) (neg_zero) e.inv)
    (by rw [ShiftedHom.mk₀_comp_mk₀, e.hom_inv_id]) (by rw [ShiftedHom.mk₀_comp_mk₀, e.inv_hom_id])
    (zero_add n)

/-- **The five lemma for continuity.** -/
lemma isHyperHContinuousAt_five
    {K₁ K₂ K₃ K₄ K₅ : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    {m₁ m₂ m₃ m₄ n₁ n₂ n₃ n₄ n₅ : ℤ}
    (β₁ : ShiftedHom K₁ K₂ m₁) (β₂ : ShiftedHom K₂ K₃ m₂) (β₃ : ShiftedHom K₃ K₄ m₃)
    (β₄ : ShiftedHom K₄ K₅ m₄) (h₁ : m₁ + n₁ = n₂) (h₂ : m₂ + n₂ = n₃) (h₃ : m₃ + n₃ = n₄)
    (h₄ : m₄ + n₄ = n₅)
    (ex₁ : ∀ T : Over S, Function.Exact (overPostcomp T β₁ h₁) (overPostcomp T β₂ h₂))
    (ex₂ : ∀ T : Over S, Function.Exact (overPostcomp T β₂ h₂) (overPostcomp T β₃ h₃))
    (ex₃ : ∀ T : Over S, Function.Exact (overPostcomp T β₃ h₃) (overPostcomp T β₄ h₄))
    (c₁ : IsHyperHContinuousAt D c K₁ n₁) (c₂ : IsHyperHContinuousAt D c K₂ n₂)
    (c₄ : IsHyperHContinuousAt D c K₄ n₄) (c₅ : IsHyperHContinuousAt D c K₅ n₅) :
    IsHyperHContinuousAt D c K₃ n₃ := by
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨i, yD, hyD⟩ := c₄.1 (overPostcomp _ β₃ h₃ x)
    have h5 : overRestrict (c.π.app i) K₅ n₅ (overPostcomp _ β₄ h₄ yD) = 0 := by
      rw [overRestrict_overPostcomp, hyD]
      exact (ex₃ c.pt).apply_apply_eq_zero x
    obtain ⟨j, g, hg⟩ := c₅.2 i _ h5
    rw [overRestrict_overPostcomp] at hg
    obtain ⟨z, hz⟩ := (ex₃ (D.obj j) (overRestrict (D.map g) K₄ n₄ yD)).1 hg
    have hker : overPostcomp c.pt β₃ h₃ (x - overRestrict (c.π.app j) K₃ n₃ z) = 0 := by
      rw [map_sub, ← overRestrict_overPostcomp, hz, overRestrict_comp, c.w g, hyD, sub_self]
    obtain ⟨w, hw⟩ := (ex₂ c.pt _).1 hker
    obtain ⟨k, w', hw'⟩ := c₂.1 w
    obtain ⟨l, a, b, -⟩ := IsCofiltered.cone_objs j k
    refine ⟨l, overRestrict (D.map a) K₃ n₃ z +
      overPostcomp _ β₂ h₂ (overRestrict (D.map b) K₂ n₂ w'), ?_⟩
    rw [map_add, overRestrict_comp, c.w a, overRestrict_overPostcomp, overRestrict_comp, c.w b,
      hw', hw, add_sub_cancel]
  · have h4 : overRestrict (c.π.app i) K₄ n₄ (overPostcomp _ β₃ h₃ y) = 0 := by
      rw [overRestrict_overPostcomp, hy, map_zero]
    obtain ⟨j, g, hg⟩ := c₄.2 i _ h4
    rw [overRestrict_overPostcomp] at hg
    obtain ⟨b, hb⟩ := (ex₂ (D.obj j) _).1 hg
    have h2 : overPostcomp c.pt β₂ h₂ (overRestrict (c.π.app j) K₂ n₂ b) = 0 := by
      rw [← overRestrict_overPostcomp, hb, overRestrict_comp, c.w g, hy]
    obtain ⟨a, ha⟩ := (ex₁ c.pt _).1 h2
    obtain ⟨k, a', ha'⟩ := c₁.1 a
    obtain ⟨l, p, q, -⟩ := IsCofiltered.cone_objs j k
    obtain ⟨m, r, hr⟩ := c₂.2 l (overRestrict (D.map p) K₂ n₂ b -
        overPostcomp _ β₁ h₁ (overRestrict (D.map q) K₁ n₁ a')) (by
      rw [map_sub, overRestrict_comp, c.w p, overRestrict_overPostcomp, overRestrict_comp, c.w q,
        ha', ha, sub_self])
    refine ⟨m, r ≫ p ≫ g, ?_⟩
    rw [map_sub, sub_eq_zero, overRestrict_overPostcomp] at hr
    rw [D.map_comp, D.map_comp, ← overRestrict_comp, ← overRestrict_comp, ← hb,
      overRestrict_overPostcomp, overRestrict_overPostcomp, hr]
    exact (ex₁ _).apply_apply_eq_zero _

end AlgebraicGeometry.Etale
