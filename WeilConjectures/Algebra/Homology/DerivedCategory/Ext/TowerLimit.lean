/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-!
# `Ext` into products and into limits of towers

Let `C` be an abelian category with K-injective resolutions in which products of shape `J` are
exact. Then `Ext X (-) n` commutes with products of shape `J`, because the localization functor
to the derived category preserves such products (`DerivedCategory.isLimitFanQ`).

For a tower `F : ℕᵒᵖ ⥤ C` such that `1 - t` is an epimorphism on `∏ Fₙ` (e.g. a tower of
epimorphisms in a replete topos), the Milnor sequence `0 ⟶ lim Fₙ ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ 0`
is short exact. If countable products are exact, its long exact `Ext`-sequence shows: if
`Ext X Fₙ q = 0` for all `n` and `q > N`, and the transition maps on `Ext X Fₙ N` are surjective,
then `Ext X (lim Fₙ) q = 0` for `q > N`.

## Main statements

- `CategoryTheory.Abelian.Ext.bijective_comp_mk₀_proj`: `Ext X (∏ Yⱼ) n ≃ ∏ Ext X Yⱼ n`.
- `CategoryTheory.Abelian.Ext.subsingleton_of_isLimit_tower`: vanishing of `Ext X (lim Fₙ) q`
  for `q > N`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite DerivedCategory

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- If products of shape `J` are exact and there are K-injective resolutions, then
`Ext X (-) n` commutes with products of shape `J`: the map `Ext X (∏ Yⱼ) n ⟶ ∏ Ext X Yⱼ n` is
bijective. -/
lemma bijective_comp_mk₀_proj [HasDerivedCategory C] [HasKInjectiveResolutions C] {J : Type*}
    [HasLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) C]
    (X : C) {Y : J → C} {P : Fan Y} (hP : IsLimit P) (n : ℕ) :
    Function.Bijective fun (x : Ext X P.pt n) (j : J) ↦ x.comp (mk₀ (P.proj j)) (add_zero n) := by
  let G := singleFunctor C 0 ⋙ shiftFunctor (DerivedCategory C) (n : ℤ)
  have : PreservesLimitsOfShape (Discrete J) ((CochainComplex.singleFunctors C).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _ (HomologicalComplex.single C _ 0))
  have : PreservesLimitsOfShape (Discrete J) (singleFunctor C 0) :=
    preservesLimitsOfShape_of_natIso (F := (CochainComplex.singleFunctors C).functor 0 ⋙ Q)
      ((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).symm
  have hG : IsLimit (G.mapCone P) := isLimitOfPreserves G hP
  have key (x : Ext X P.pt n) (j : J) :
      (x.comp (mk₀ (P.proj j)) (add_zero n)).hom = x.hom ≫ G.map (P.proj j) := by
    simp [G, ShiftedHom.comp_mk₀]
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · ext
    refine hG.hom_ext fun ⟨j⟩ ↦ ?_
    have h' := congrArg Ext.hom (congrFun h j)
    rw [key, key] at h'
    exact h'
  · refine ⟨homEquiv.symm (hG.lift (Cone.mk _ (Discrete.natTrans fun j ↦ (z j.as).hom))),
      funext fun j ↦ ?_⟩
    ext
    rw [key, hom, Equiv.apply_symm_apply]
    exact hG.fac _ ⟨j⟩
/-- Let `F : ℕᵒᵖ ⥤ C` be a tower with limit `c` such that `1 - t` is an epimorphism on products
of the tower, where `t` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. Assume countable products are exact.
If `Ext X Fₙ q = 0` for all `n` and `q > N`, and the transition maps `Ext X Fₙ₊₁ N ⟶ Ext X Fₙ N`
are surjective, then `Ext X (lim Fₙ) q = 0` for `q > N`. This follows from the long exact
`Ext`-sequence of the Milnor sequence `0 ⟶ lim Fₙ ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ 0`, since `1 - t`
induces `1 - t` on `∏ Ext X Fₙ N`, which is surjective. -/
theorem subsingleton_of_isLimit_tower [HasDerivedCategory C] [HasKInjectiveResolutions C]
    [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C] (X : C) {F : ℕᵒᵖ ⥤ C}
    (hF : ∀ ⦃P : Fan fun n : ℕ ↦ F.obj (op n)⦄ (_ : IsLimit P) (t : P.pt ⟶ P.pt),
      (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) →
        Epi (𝟙 P.pt - t))
    {c : Cone F} (hc : IsLimit c) (N : ℕ)
    (hvan : ∀ n q, N < q → Subsingleton (Ext X (F.obj (op n)) q))
    (hsurj : ∀ n, Function.Surjective fun x : Ext X (F.obj (op (n + 1))) N ↦
      x.comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero N))
    (q : ℕ) (hq : N < q) : Subsingleton (Ext X c.pt q) := by
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
  have hφ (m : ℕ) := bijective_comp_mk₀_proj X hP m
  have hsub (m : ℕ) (hm : N < m) : Subsingleton (Ext X P.pt m) :=
    have := fun n ↦ hvan n m hm
    (hφ m).1.subsingleton
  -- `1 - t` induces a surjection on `Ext X (∏ Fₙ) m` for `m ≥ N`.
  have hg (m : ℕ) (hm : N ≤ m) (y : Ext X P.pt m) :
      ∃ z : Ext X P.pt m, z.comp (mk₀ S.g) (add_zero m) = y := by
    obtain hm | rfl := hm.lt_or_eq
    · have := hsub m hm
      exact ⟨0, Subsingleton.elim _ _⟩
    let w (n : ℕ) := y.comp (mk₀ (P.proj n)) (add_zero N)
    let a (n : ℕ) : Ext X (F.obj (op n)) N :=
      Nat.rec (motive := fun n ↦ Ext X (F.obj (op n)) N) 0
        (fun n an ↦ (hsurj n (an - w n)).choose) n
    have ha (n : ℕ) : (a (n + 1)).comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero N) =
        a n - w n :=
      (hsurj n _).choose_spec
    obtain ⟨z, hz⟩ := (hφ N).2 a
    refine ⟨z, (hφ N).1 (funext fun n ↦ ?_)⟩
    have hz' (k : ℕ) : z.comp (mk₀ (P.proj k)) (add_zero N) = a k := congrFun hz k
    have e : S.g ≫ P.proj n = P.proj n + -(P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) := by
      simp [S, ht, sub_eq_add_neg]
    have hneg {A B : C} (f : A ⟶ B) : mk₀ (-f) = -mk₀ f :=
      eq_neg_of_add_eq_zero_left (by rw [← mk₀_add, neg_add_cancel, mk₀_zero])
    dsimp only
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, e, mk₀_add, hneg, ← mk₀_comp_mk₀, comp_add,
      comp_neg, ← comp_assoc_of_third_deg_zero, hz', hz', ha]
    simp [w]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by lia⟩
  have := hsub (m + 1) hq
  obtain ⟨x₃, rfl⟩ := covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) rfl
  obtain ⟨z, rfl⟩ := hg m (by lia) x₃
  rw [comp_assoc_of_second_deg_zero, hS.comp_extClass, comp_zero]

end CategoryTheory.Abelian.Ext
