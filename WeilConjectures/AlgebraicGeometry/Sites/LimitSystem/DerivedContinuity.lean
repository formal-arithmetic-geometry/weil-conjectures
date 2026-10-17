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
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} {m m' n n' : ℤ}
    (β : ShiftedHom K L m) (γ : ShiftedHom L K m') (hm : m' + m = 0) (hm' : m + m' = 0)
    (hβγ : β.comp γ hm = ShiftedHom.mk₀ 0 rfl (𝟙 K))
    (hγβ : γ.comp β hm' = ShiftedHom.mk₀ 0 rfl (𝟙 L)) (h : m + n = n')
    (hK : IsHyperHContinuousAt D c K n) : IsHyperHContinuousAt D c L n' := by
  have h' : m' + n' = n := by omega
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
  hK.of_shiftedHom (ShiftedHom.mk₀ 0 rfl e.hom) (ShiftedHom.mk₀ 0 rfl e.inv) (add_zero 0)
    (add_zero 0) (by rw [ShiftedHom.mk₀_comp_mk₀, e.hom_inv_id])
    (by rw [ShiftedHom.mk₀_comp_mk₀, e.inv_hom_id]) (zero_add n)

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

section Triangle

variable (T : Over S)
  {Tr : Triangle (DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))}
  (hTr : Tr ∈ distTriang _)

/-- The functor `Hom(ℤ_T, -)` on the derived category of `T`. -/
private noncomputable abbrev coyo :=
  preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor
    (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj (unitSheaf T.left)))

private lemma overPostcomp_mk₀_eq {K L : DerivedCategory (Sheaf S.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (f : K ⟶ L) (n : ℤ) :
    ⇑(overPostcomp T (ShiftedHom.mk₀ 0 rfl f) (zero_add n)) =
      fun x ↦ ((coyo T).shift n).map ((overPullback T).map f) x := by
  ext x
  simp only [overPostcomp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ShiftedHom.map_mk₀,
    ShiftedHom.comp_mk₀]
  rfl

private lemma overPostcomp_mor₃_eq {n₀ n₁ : ℤ} (h : 1 + n₀ = n₁) :
    ⇑(overPostcomp T (Tr.mor₃ : ShiftedHom Tr.obj₃ Tr.obj₁ (1 : ℤ)) h) =
      fun x ↦ (coyo T).homologySequenceδ ((overPullback T).mapTriangle.obj Tr) n₀ n₁
        (by omega) x := by
  ext x
  rw [preadditiveCoyoneda_homologySequenceδ_apply]
  rfl

include hTr

lemma exact_overPostcomp_mor₁_mor₂ (n : ℤ) :
    Function.Exact (overPostcomp T (ShiftedHom.mk₀ 0 rfl Tr.mor₁) (zero_add n))
      (overPostcomp T (ShiftedHom.mk₀ 0 rfl Tr.mor₂) (zero_add n)) := by
  have := (coyo T).homologySequence_exact₂ _ ((overPullback T).map_distinguished Tr hTr) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  rw [overPostcomp_mk₀_eq, overPostcomp_mk₀_eq]
  exact this

lemma exact_overPostcomp_mor₂_mor₃ {n₀ n₁ : ℤ} (h : 1 + n₀ = n₁) :
    Function.Exact (overPostcomp T (ShiftedHom.mk₀ 0 rfl Tr.mor₂) (zero_add n₀))
      (overPostcomp T (Tr.mor₃ : ShiftedHom Tr.obj₃ Tr.obj₁ (1 : ℤ)) h) := by
  have := (coyo T).homologySequence_exact₃ _ ((overPullback T).map_distinguished Tr hTr) n₀ n₁
    (by omega)
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  rw [overPostcomp_mk₀_eq, overPostcomp_mor₃_eq]
  exact this

lemma exact_overPostcomp_mor₃_mor₁ {n₀ n₁ : ℤ} (h : 1 + n₀ = n₁) :
    Function.Exact (overPostcomp T (Tr.mor₃ : ShiftedHom Tr.obj₃ Tr.obj₁ (1 : ℤ)) h)
      (overPostcomp T (ShiftedHom.mk₀ 0 rfl Tr.mor₁) (zero_add n₁)) := by
  have := (coyo T).homologySequence_exact₁ _ ((overPullback T).map_distinguished Tr hTr) n₀ n₁
    (by omega)
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  rw [overPostcomp_mk₀_eq, overPostcomp_mor₃_eq]
  exact this

omit T

/-- Continuity along the middle term of a distinguished triangle. -/
lemma isHyperHContinuousAt_obj₂ (n : ℤ)
    (h₃ : IsHyperHContinuousAt D c Tr.obj₃ (n - 1)) (h₁ : IsHyperHContinuousAt D c Tr.obj₁ n)
    (h₃' : IsHyperHContinuousAt D c Tr.obj₃ n) (h₁' : IsHyperHContinuousAt D c Tr.obj₁ (n + 1)) :
    IsHyperHContinuousAt D c Tr.obj₂ n :=
  isHyperHContinuousAt_five (Tr.mor₃ : ShiftedHom Tr.obj₃ Tr.obj₁ (1 : ℤ))
    (ShiftedHom.mk₀ 0 rfl Tr.mor₁) (ShiftedHom.mk₀ 0 rfl Tr.mor₂)
    (Tr.mor₃ : ShiftedHom Tr.obj₃ Tr.obj₁ (1 : ℤ)) (by omega) (zero_add n) (zero_add n)
    (add_comm 1 n) (fun T ↦ exact_overPostcomp_mor₃_mor₁ T hTr _)
    (fun T ↦ exact_overPostcomp_mor₁_mor₂ T hTr n) (fun T ↦ exact_overPostcomp_mor₂_mor₃ T hTr _)
    h₃ h₁ h₃' h₁'

end Triangle

section Bounded

lemma subsingleton_hyperH_of_isGE (T : Over S)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ)
    [K.IsGE (n + 1)] : Subsingleton (hyperH ((overPullback T).obj K) n) := by
  have : ((overPullback T).obj K).IsGE (n + 1) :=
    Functor.isGE_mapDerivedCategory_obj _ K (n + 1)
  have : DerivedCategory.TStructure.t.IsGE (((overPullback T).obj K)⟦n⟧) 1 :=
    DerivedCategory.TStructure.t.isGE_shift _ (n + 1) n 1 (by omega)
  refine ⟨fun x y ↦ ?_⟩
  rw [DerivedCategory.TStructure.t.zero (X := (DerivedCategory.singleFunctor _ 0).obj _)
    (show _ ⟶ _ from x) 0 1, DerivedCategory.TStructure.t.zero
    (X := (DerivedCategory.singleFunctor _ 0).obj _) (show _ ⟶ _ from y) 0 1]

/-- Continuity is stable under shifts. -/
lemma IsHyperHContinuousAt.shift
    {K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} (m : ℤ) {n : ℤ}
    (hK : IsHyperHContinuousAt D c K (n + m)) : IsHyperHContinuousAt D c (K⟦m⟧) n := by
  refine hK.of_shiftedHom (m := -m) (m' := m)
    ((shiftFunctorCompIsoId _ m (-m) (add_neg_cancel m)).inv.app K : K ⟶ K⟦m⟧⟦-m⟧)
    (𝟙 (K⟦m⟧) : K⟦m⟧ ⟶ K⟦m⟧) (add_neg_cancel m) (neg_add_cancel m) ?_ ?_ (by omega)
  · simp [ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorCompIsoId, shiftFunctorZero']
  · simp only [ShiftedHom.comp, ShiftedHom.mk₀, Functor.map_id, Category.id_comp]
    rw [shift_shiftFunctorCompIsoId_inv_app]
    simp [shiftFunctorCompIsoId, shiftFunctorZero']

variable (D c) in
/-- Hypothesis: continuity for single sheaves in degree `0`. -/
def SingleContinuity : Prop :=
  ∀ (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℤ),
    IsHyperHContinuousAt D c ((DerivedCategory.singleFunctor _ 0).obj F) n

lemma isHyperHContinuousAt_singleFunctor (hs : SingleContinuity D c)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (a n : ℤ) :
    IsHyperHContinuousAt D c ((DerivedCategory.singleFunctor _ a).obj F) n :=
  ((hs F (n + -a)).shift (-a)).of_iso
    (((DerivedCategory.singleFunctors _).shiftIso (-a) a 0 (by omega)).app F)

lemma isHyperHContinuousAt_of_isGE_of_isLE_self (hs : SingleContinuity D c) (a : ℤ)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) [K.IsGE a]
    [K.IsLE a] (n : ℤ) : IsHyperHContinuousAt D c K n := by
  obtain ⟨Y, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  exact (isHyperHContinuousAt_singleFunctor hs Y a n).of_iso e.symm

lemma isHyperHContinuousAt_of_isGE_of_isLE (hs : SingleContinuity D c) (d : ℕ) :
    ∀ (a : ℤ) (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))
      [K.IsGE a] [K.IsLE (a + d)] (n : ℤ), IsHyperHContinuousAt D c K n := by
  induction d with
  | zero =>
    intro a K _ hK n
    have : K.IsLE a := by simpa using hK
    exact isHyperHContinuousAt_of_isGE_of_isLE_self hs a K n
  | succ d ih =>
    intro a K _ hK n
    let t := DerivedCategory.TStructure.t (C := Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    have hTr := t.triangleLEGE_distinguished (a + d) (a + d + 1) rfl K
    have : K.IsLE (a + d + 1) := by
      have h := hK
      rwa [Nat.cast_add, Nat.cast_one, ← add_assoc] at h
    have : ((t.truncLE (a + d)).obj K).IsLE (a + (d : ℕ)) := by
      change t.IsLE _ _; infer_instance
    have : ((t.truncLE (a + d)).obj K).IsGE a := by
      change t.IsGE _ _; infer_instance
    have : ((t.truncGE (a + d + 1)).obj K).IsGE (a + d + 1) := by
      change t.IsGE _ _; infer_instance
    have : ((t.truncGE (a + d + 1)).obj K).IsLE (a + d + 1) := by
      change t.IsLE _ _; infer_instance
    have h₁ (m : ℤ) := ih a ((t.truncLE (a + d)).obj K) m
    have h₃ (m : ℤ) := isHyperHContinuousAt_of_isGE_of_isLE_self hs (a + d + 1)
      ((t.truncGE (a + d + 1)).obj K) m
    exact isHyperHContinuousAt_obj₂ hTr n (h₃ _) (h₁ n) (h₃ n) (h₁ _)

/-- Continuity for bounded below complexes, given continuity for single sheaves. -/
lemma isHyperHContinuousAt_of_isGE (hs : SingleContinuity D c) (a : ℤ)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) [K.IsGE a]
    (n : ℤ) : IsHyperHContinuousAt D c K n := by
  let t := DerivedCategory.TStructure.t (C := Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
  have hTr := t.triangleLEGE_distinguished (n + 1) (n + 2) (by ring) K
  have : ((t.truncLE (n + 1)).obj K).IsGE a := by
    change t.IsGE _ _; infer_instance
  have : ((t.truncLE (n + 1)).obj K).IsLE (a + ((n + 1 - a).toNat : ℕ)) := by
    have : ((t.truncLE (n + 1)).obj K).IsLE (n + 1) := by change t.IsLE _ _; infer_instance
    exact t.isLE_of_le _ (n + 1) _ (by omega)
  have : ((t.truncGE (n + 2)).obj K).IsGE (n - 1 + 1) := by
    change t.IsGE _ _; exact t.isGE_of_ge _ _ (n + 2) (by omega)
  have : ((t.truncGE (n + 2)).obj K).IsGE (n + 1) := by
    change t.IsGE _ _; exact t.isGE_of_ge _ _ (n + 2) (by omega)
  have h₁ (m : ℤ) := isHyperHContinuousAt_of_isGE_of_isLE hs _ a ((t.truncLE (n + 1)).obj K) m
  exact isHyperHContinuousAt_obj₂ hTr n
    (isHyperHContinuousAt_of_subsingleton fun T ↦ subsingleton_hyperH_of_isGE T _ (n - 1))
    (h₁ n) (isHyperHContinuousAt_of_subsingleton fun T ↦ subsingleton_hyperH_of_isGE T _ n)
    (h₁ _)

end Bounded

section Single

variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]

/-- Continuity for single sheaves: this is
`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`. -/
lemma singleContinuity_of_isLimit (hc : IsLimit ((Over.forget S).mapCone c)) :
    SingleContinuity D c := by
  intro F n
  rcases lt_or_ge n 0 with hn | hn
  · refine isHyperHContinuousAt_of_subsingleton fun T ↦ ?_
    have : ((DerivedCategory.singleFunctor _ 0).obj F).IsGE (n + 1) :=
      DerivedCategory.TStructure.t.isGE_of_ge _ (n + 1) 0 (by omega)
    exact subsingleton_hyperH_of_isGE T _ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨hs, hi⟩ := cohomologyMap_isColimit_of_isLimit F D c hc q
    refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
    · obtain ⟨e, rfl⟩ := (sheafHToHyperH_bijective F c.pt q).2 x
      obtain ⟨i, y, hy⟩ := hs e
      refine ⟨i, sheafHToHyperH F (D.obj i) q y, ?_⟩
      rw [overRestrict_sheafHToHyperH, hy, ← Sheaf.H.map_comp_apply, Iso.hom_inv_id_app,
        Sheaf.H.map_id_apply]
    · obtain ⟨e, rfl⟩ := (sheafHToHyperH_bijective F (D.obj i) q).2 y
      rw [overRestrict_sheafHToHyperH, ← sheafHToHyperH_zero F c.pt q] at hy
      have h0 := (sheafHToHyperH_bijective F c.pt q).1 hy
      obtain ⟨j, g, hg⟩ := hi i e (eq_zero_of_sheafH_map_eq_zero _ h0)
      refine ⟨j, g, ?_⟩
      rw [overRestrict_sheafHToHyperH, hg, map_zero, sheafHToHyperH_zero]

end Single

/-- Blueprint `lem-weil-pbc-derived-cohomology-continuity`: Continuity for bounded-below étale
complexes.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `K` be a bounded below complex of abelian étale
sheaves on `S`. Then the hypercohomology `Hⁿ(X, K|_X) = Hom(ℤ_X, K|_X[n])` is the colimit of the
`Hⁿ(Dᵢ, K|_{Dᵢ})` along the restriction maps `AlgebraicGeometry.Etale.overRestrict`: every class
on `X` comes from some `Dᵢ`, and a class on `Dᵢ` which vanishes on `X` already vanishes on some
`Dⱼ`, `j ⟶ i`. -/
theorem isHyperHContinuousAt_of_isLimit {S : Scheme.{u}} {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) (a : ℤ) [K.IsGE a]
    (n : ℤ) : IsHyperHContinuousAt D c K n :=
  isHyperHContinuousAt_of_isGE (singleContinuity_of_isLimit hc) a K n

end AlgebraicGeometry.Etale
