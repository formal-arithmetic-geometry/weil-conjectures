/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.Exact.Basic

/-! # Co-special triangle criterion for distinguishedness

Source: literature/stacks-project/derived.tex, Tags 014A and 09WA,
Remark 13.3.6 and Lemma 13.3.7 (blueprint: lem-sp-roos-special-triangle-iso).

## Main definitions

* `CategoryTheory.Pretriangulated.IsCoSpecial` records exactness of the
  representable Hom sequence in all integer shifts.
* `CategoryTheory.Pretriangulated.directSumTriangle` is the componentwise
  biproduct triangle.

## Main statement

* `CategoryTheory.Pretriangulated.roos_special_triangle_iso` gives the co-special
  criterion for distinguished triangles, direct sums, and two-out-of-three.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangle is co-special when every shifted representable Hom sequence is exact.

Source: literature/stacks-project/derived.tex, Remark 13.3.6 and Lemma 13.3.7
(Tags 09WA and 014A); (blueprint: lem-sp-roos-special-triangle-iso).
The three middle-term exactness conditions for the triangle, its rotation, and
its inverse rotation are exactly the three kinds of terms in the long sequence.
-/
def IsCoSpecial (T : Triangle C) : Prop :=
  ∀ (W : C) (n : ℤ),
    Function.Exact
        (fun (x : T.obj₃⟦n⟧ ⟶ W) ↦ T.mor₂⟦n⟧' ≫ x)
        (fun (x : T.obj₂⟦n⟧ ⟶ W) ↦ T.mor₁⟦n⟧' ≫ x) ∧
    Function.Exact
        (fun (x : T.rotate.obj₃⟦n⟧ ⟶ W) ↦ T.rotate.mor₂⟦n⟧' ≫ x)
        (fun (x : T.rotate.obj₂⟦n⟧ ⟶ W) ↦ T.rotate.mor₁⟦n⟧' ≫ x) ∧
    Function.Exact
        (fun (x : T.invRotate.obj₃⟦n⟧ ⟶ W) ↦ T.invRotate.mor₂⟦n⟧' ≫ x)
        (fun (x : T.invRotate.obj₂⟦n⟧ ⟶ W) ↦ T.invRotate.mor₁⟦n⟧' ≫ x)

/-- The componentwise biproduct of two triangles, using the shifted biproduct injections.

Source: literature/stacks-project/derived.tex, Tag 05QS (lemma-direct-sum-triangles);
(blueprint: lem-sp-roos-special-triangle-iso).
-/
def directSumTriangle (T₁ T₂ : Triangle C) : Triangle C :=
  Triangle.mk (biprod.map T₁.mor₁ T₂.mor₁) (biprod.map T₁.mor₂ T₂.mor₂)
    (biprod.desc (T₁.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inl)
      (T₂.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inr))

private abbrev HomExact (T : Triangle C) (F : C ⥤ C) (W : C) : Prop :=
  Function.Exact (fun (x : F.obj T.obj₃ ⟶ W) ↦ F.map T.mor₂ ≫ x)
    (fun (x : F.obj T.obj₂ ⟶ W) ↦ F.map T.mor₁ ≫ x)

private lemma distinguished_homExact (T : Triangle C) (hT : T ∈ distTriang C)
    (W : C) (n : ℤ) : HomExact T (shiftFunctor C n) W := by
  intro y
  change T.mor₁⟦n⟧' ≫ y = 0 ↔ ∃ x, T.mor₂⟦n⟧' ≫ x = y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ _ (Triangle.shift_distinguished T hT n) y
      (by
        change (n.negOnePow • T.mor₁⟦n⟧') ≫ y = 0
        rw [Linear.units_smul_comp, hy, smul_zero])
    change y = (n.negOnePow • T.mor₂⟦n⟧') ≫ x at hx
    refine ⟨n.negOnePow • x, ?_⟩
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul] using hx.symm
  · rintro ⟨x, rfl⟩
    simp only [← Category.assoc, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero, zero_comp]

private lemma distinguished_coSpecial (T : Triangle C) (hT : T ∈ distTriang C) :
    IsCoSpecial T := by
  intro W n
  exact ⟨distinguished_homExact T hT W n,
    distinguished_homExact _ (rot_of_distTriang T hT) W n,
    distinguished_homExact _ (inv_rot_of_distTriang T hT) W n⟩

omit [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc]
private lemma mapped_comm₁ (F : C ⥤ C) {T S : Triangle C} (a : T ⟶ S) :
    F.map T.mor₁ ≫ F.map a.hom₂ = F.map a.hom₁ ≫ F.map S.mor₁ := by
  rw [← F.map_comp, a.comm₁, F.map_comp]

omit [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc]
private lemma mapped_comm₂ (F : C ⥤ C) {T S : Triangle C} (a : T ⟶ S) :
    F.map T.mor₂ ≫ F.map a.hom₃ = F.map a.hom₂ ≫ F.map S.mor₂ := by
  rw [← F.map_comp, a.comm₂, F.map_comp]

-- Exactness is inherited by a retract of a diagram.
omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma homExact_retract {T S : Triangle C} (i : T ⟶ S) (p : S ⟶ T)
    (hi : i ≫ p = 𝟙 T) (F : C ⥤ C) [F.Additive] (W : C)
    (hS : HomExact S F W) : HomExact T F W := by
  have h₁ : F.map i.hom₁ ≫ F.map p.hom₁ = 𝟙 _ := by
    rw [← F.map_comp, ← comp_hom₁, hi, id_hom₁, F.map_id]
  have h₂ : F.map i.hom₂ ≫ F.map p.hom₂ = 𝟙 _ := by
    rw [← F.map_comp, ← comp_hom₂, hi, id_hom₂, F.map_id]
  intro y
  change F.map T.mor₁ ≫ y = 0 ↔ ∃ x, F.map T.mor₂ ≫ x = y
  constructor
  · intro hy
    have hz : F.map S.mor₁ ≫ (F.map p.hom₂ ≫ y) = 0 := by
      rw [← F.map_comp_assoc, p.comm₁, F.map_comp, Category.assoc, hy, comp_zero]
    obtain ⟨x, hx⟩ := (hS _).mp hz
    dsimp only at hx
    refine ⟨F.map i.hom₃ ≫ x, ?_⟩
    rw [← F.map_comp_assoc, i.comm₂, F.map_comp, Category.assoc, hx,
      ← Category.assoc, h₂, id_comp]
  · rintro ⟨x, rfl⟩
    have hz := hS.apply_apply_eq_zero (F.map p.hom₃ ≫ x)
    have hz' := congrArg (fun z ↦ F.map i.hom₁ ≫ z) hz
    simp only [mapped_comm₂_assoc F p, mapped_comm₁_assoc F p] at hz'
    simpa only [← Category.assoc, h₁, id_comp, comp_zero] using hz'

-- Conversely, the sum of the two projection-inclusion composites is enough to
-- assemble the coordinate preimages. Orthogonality is not needed for this direction.
omit [HasZeroObject C] [Pretriangulated C] in
private lemma homExact_sum {T₁ T₂ S : Triangle C}
    (i₁ : T₁ ⟶ S) (p₁ : S ⟶ T₁) (i₂ : T₂ ⟶ S) (p₂ : S ⟶ T₂)
    (hs : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 S)
    (F : C ⥤ C) [F.Additive] (W : C)
    (hT₁ : HomExact T₁ F W) (hT₂ : HomExact T₂ F W) : HomExact S F W := by
  have h₁ : F.map p₁.hom₁ ≫ F.map i₁.hom₁ +
      F.map p₂.hom₁ ≫ F.map i₂.hom₁ = 𝟙 _ := by
    simpa only [F.map_add, F.map_comp, Triangle.add_hom₁, comp_hom₁,
      id_hom₁, F.map_id] using congrArg (fun f ↦ F.map f.hom₁) hs
  have h₂ : F.map p₁.hom₂ ≫ F.map i₁.hom₂ +
      F.map p₂.hom₂ ≫ F.map i₂.hom₂ = 𝟙 _ := by
    simpa only [F.map_add, F.map_comp, Triangle.add_hom₂, comp_hom₂,
      id_hom₂, F.map_id] using congrArg (fun f ↦ F.map f.hom₂) hs
  intro y
  change F.map S.mor₁ ≫ y = 0 ↔ ∃ x, F.map S.mor₂ ≫ x = y
  constructor
  · intro hy
    have hz₁ : F.map T₁.mor₁ ≫ (F.map i₁.hom₂ ≫ y) = 0 := by
      rw [← F.map_comp_assoc, i₁.comm₁, F.map_comp, Category.assoc, hy, comp_zero]
    have hz₂ : F.map T₂.mor₁ ≫ (F.map i₂.hom₂ ≫ y) = 0 := by
      rw [← F.map_comp_assoc, i₂.comm₁, F.map_comp, Category.assoc, hy, comp_zero]
    obtain ⟨x₁, hx₁⟩ := (hT₁ _).mp hz₁
    obtain ⟨x₂, hx₂⟩ := (hT₂ _).mp hz₂
    dsimp only at hx₁ hx₂
    refine ⟨F.map p₁.hom₃ ≫ x₁ + F.map p₂.hom₃ ≫ x₂, ?_⟩
    rw [Preadditive.comp_add, ← F.map_comp_assoc, ← F.map_comp_assoc,
      p₁.comm₂, p₂.comm₂, F.map_comp, F.map_comp,
      Category.assoc, Category.assoc, hx₁, hx₂, ← Category.assoc, ← Category.assoc,
      ← Preadditive.add_comp, h₂, id_comp]
  · rintro ⟨x, rfl⟩
    have hz₁ := hT₁.apply_apply_eq_zero (F.map i₁.hom₃ ≫ x)
    have hz₂ := hT₂.apply_apply_eq_zero (F.map i₂.hom₃ ≫ x)
    calc
      F.map S.mor₁ ≫ (F.map S.mor₂ ≫ x) =
          (F.map p₁.hom₁ ≫ F.map i₁.hom₁ +
            F.map p₂.hom₁ ≫ F.map i₂.hom₁) ≫
              (F.map S.mor₁ ≫ (F.map S.mor₂ ≫ x)) := by rw [h₁, id_comp]
      _ = F.map p₁.hom₁ ≫ (F.map T₁.mor₁ ≫ (F.map T₁.mor₂ ≫
            (F.map i₁.hom₃ ≫ x))) +
          F.map p₂.hom₁ ≫ (F.map T₂.mor₁ ≫ (F.map T₂.mor₂ ≫
            (F.map i₂.hom₃ ≫ x))) := by
        simp only [Preadditive.add_comp, Category.assoc,
          ← mapped_comm₁_assoc F i₁, ← mapped_comm₁_assoc F i₂,
          ← mapped_comm₂_assoc F i₁, ← mapped_comm₂_assoc F i₂]
      _ = 0 := by rw [hz₁, hz₂, comp_zero, comp_zero, add_zero]

private def sumInl (T₁ T₂ : Triangle C) : T₁ ⟶ directSumTriangle T₁ T₂ where
  hom₁ := biprod.inl
  hom₂ := biprod.inl
  hom₃ := biprod.inl
  comm₁ := by simp [directSumTriangle]
  comm₂ := by simp [directSumTriangle]
  comm₃ := by simp [directSumTriangle]

private def sumInr (T₁ T₂ : Triangle C) : T₂ ⟶ directSumTriangle T₁ T₂ where
  hom₁ := biprod.inr
  hom₂ := biprod.inr
  hom₃ := biprod.inr
  comm₁ := by simp [directSumTriangle]
  comm₂ := by simp [directSumTriangle]
  comm₃ := by simp [directSumTriangle]

private def sumFst (T₁ T₂ : Triangle C) : directSumTriangle T₁ T₂ ⟶ T₁ where
  hom₁ := biprod.fst
  hom₂ := biprod.fst
  hom₃ := biprod.fst
  comm₁ := by simp [directSumTriangle]
  comm₂ := by simp [directSumTriangle]
  comm₃ := by
    dsimp [directSumTriangle, Triangle.mk]
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]

private def sumSnd (T₁ T₂ : Triangle C) : directSumTriangle T₁ T₂ ⟶ T₂ where
  hom₁ := biprod.snd
  hom₂ := biprod.snd
  hom₃ := biprod.snd
  comm₁ := by simp [directSumTriangle]
  comm₂ := by simp [directSumTriangle]
  comm₃ := by
    dsimp [directSumTriangle, Triangle.mk]
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma unshift_homExact (T : Triangle C) (W : C)
    (h : HomExact T (shiftFunctor C (0 : ℤ)) W) : HomExact T (𝟭 C) W := by
  apply homExact_retract ((Triangle.shiftFunctorZero C).inv.app T)
    ((Triangle.shiftFunctorZero C).hom.app T) (by simp) (𝟭 C) W
  simpa only [HomExact, Triangle.shiftFunctor, Triangle.mk,
    Int.negOnePow_zero, one_smul, Functor.id_map, Functor.id_obj] using h

omit [HasZeroObject C] [Pretriangulated C] in
private lemma invRotate_shift_mor₁ (T : Triangle C) :
    T.invRotate.mor₁⟦(1 : ℤ)⟧' =
      -((shiftEquiv C (1 : ℤ)).counitIso.hom.app T.obj₃ ≫ T.mor₃) := by
  simp only [Triangle.invRotate_mor₁, Functor.map_comp, Functor.map_neg,
    shiftEquiv'_counitIso,
    shift_shiftFunctorCompIsoId_hom_app, shift_neg_shift',
    Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, comp_id]

private lemma comparison_isIso {T T' : Triangle C} (hT : IsCoSpecial T)
    (hT' : T' ∈ distTriang C) (φ : T ⟶ T')
    [IsIso φ.hom₁] [IsIso φ.hom₂] : IsIso φ.hom₃ := by
  have ex₂ (W : C) := unshift_homExact T W (hT W 0).1
  have ex₃ (W : C) := unshift_homExact T.rotate W (hT W 0).2.1
  have hc : Epi φ.hom₃ := by
    rw [epi_iff_cancel_zero]
    intro W x hx
    obtain ⟨z, hz⟩ := Triangle.yoneda_exact₃ T' hT' x (by
      rw [← cancel_epi φ.hom₂, comp_zero, ← Category.assoc, ← φ.comm₂,
        Category.assoc, hx, comp_zero])
    have hk : T.mor₃ ≫ (φ.hom₁⟦(1 : ℤ)⟧' ≫ z) = 0 := by
      rw [← Category.assoc, φ.comm₃, Category.assoc, ← hz, hx]
    obtain ⟨w, hw⟩ := ((hT W 1).2.2 (φ.hom₁⟦(1 : ℤ)⟧' ≫ z)).mp (by
      change T.invRotate.mor₁⟦(1 : ℤ)⟧' ≫ (φ.hom₁⟦(1 : ℤ)⟧' ≫ z) = 0
      rw [invRotate_shift_mor₁, neg_comp, Category.assoc, hk, comp_zero, neg_zero])
    change T.mor₁⟦(1 : ℤ)⟧' ≫ w = φ.hom₁⟦(1 : ℤ)⟧' ≫ z at hw
    have hz' : z = T'.mor₁⟦(1 : ℤ)⟧' ≫ inv (φ.hom₂⟦(1 : ℤ)⟧') ≫ w := by
      rw [← cancel_epi (φ.hom₁⟦(1 : ℤ)⟧'), ← hw]
      have he := congrArg (fun f ↦ f⟦(1 : ℤ)⟧') φ.comm₁
      simp only [Functor.map_comp] at he
      rw [← Category.assoc, ← he, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [hz, hz', ← Category.assoc, comp_distTriang_mor_zero₃₁ T' hT', zero_comp]
  let := hc
  apply isIso_of_coyoneda_map_bijective
  intro W
  refine ⟨fun x y h ↦ (cancel_epi φ.hom₃).mp h, ?_⟩
  intro y
  have hy : T'.mor₁ ≫ (inv φ.hom₂ ≫ T.mor₂ ≫ y) = 0 := by
    rw [← cancel_epi φ.hom₁, comp_zero, ← Category.assoc, ← φ.comm₁,
      Category.assoc, IsIso.hom_inv_id_assoc]
    exact (ex₂ W).apply_apply_eq_zero y
  obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ T' hT' _ hy
  have hd : T.mor₂ ≫ (y - φ.hom₃ ≫ x) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc T.mor₂ φ.hom₃ x, φ.comm₂,
      Category.assoc, ← hx, IsIso.hom_inv_id_assoc, sub_self]
  obtain ⟨z, hz⟩ : ∃ (z : T.obj₁⟦(1 : ℤ)⟧ ⟶ W),
      T.mor₃ ≫ z = y - φ.hom₃ ≫ x := (ex₃ W _).mp hd
  refine ⟨x + T'.mor₃ ≫ inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ z, ?_⟩
  dsimp only
  rw [Preadditive.comp_add, ← Category.assoc φ.hom₃ T'.mor₃, ← φ.comm₃,
    Category.assoc, IsIso.hom_inv_id_assoc, hz, add_sub_cancel]

/-- Co-special triangles, direct sums, and the two-out-of-three criterion.

Source: literature/stacks-project/derived.tex, Remark 13.3.6 and Lemma 13.3.7
(Tags 09WA and 014A), with the direct-sum argument of Tag 05QS;
(blueprint: lem-sp-roos-special-triangle-iso).
Proof plan (the four steps of the DAG node).
1. Apply `lem-sp-roos-triangle-hom-exact` to a distinguished triangle and its
   rotations and shifts, giving all three exactness conditions for every W and n.
2. The biproduct identities of `def-weil-additive-category` identify Hom(A ⊞ B, W)
   with Hom(A, W) × Hom(B, W), inversely sending (u, v) to p_A ≫ u + p_B ≫ v.
   Shifts preserve these identities. The sequence maps become diagonal. Exactness
   of both coordinates gives exactness of the sum by taking coordinate preimages;
   exactness of the sum gives exactness of each coordinate by embedding (y, 0) or
   (0, y), taking a preimage, and projecting. Composites vanish coordinatewise.
3. For a triangle morphism (a, b, c) with a, b invertible, chase the five-term
   Hom(-, W) sequences directly. If c ≫ x = 0, exactness of the distinguished T'
   gives x = h' ≫ z; then h ≫ a[1] ≫ z = 0, so co-special exactness of
   T.invRotate shifted by 1 (its first arrow is -h after the shift counit) gives
   a[1] ≫ z = f[1] ≫ w, hence z = f'[1] ≫ b[1]⁻¹ ≫ w and x = 0: c is epic. For
   y : Z → W, exactness of T' gives x with g' ≫ x = b⁻¹ ≫ g ≫ y; then
   g ≫ (y - c ≫ x) = 0 and co-special exactness of T.rotate gives z with
   h ≫ z = y - c ≫ x, so c ≫ (x + h' ≫ a[1]⁻¹ ≫ z) = y. Precomposition with c is
   bijective for every W, and `isIso_of_coyoneda_map_bijective` makes c an iso.
4. The component inverses form the inverse triangle morphism: multiply each square
   by adjacent inverses, using that the shift of a inverse is inverse to the shift
   of a. The composites are vertexwise identities. TR1 from
   `def-weil-triangulated-category` transports distinguishedness to the source.
-/
theorem roos_special_triangle_iso
    {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    (∀ (T : Triangle C), T ∈ distTriang C → IsCoSpecial T) ∧
    (∀ (T₁ T₂ : Triangle C),
      IsCoSpecial (directSumTriangle T₁ T₂) ↔ IsCoSpecial T₁ ∧ IsCoSpecial T₂) ∧
    (∀ {T T' : Triangle C}, IsCoSpecial T → T' ∈ distTriang C →
      (φ : T ⟶ T') → IsIso φ.hom₁ → IsIso φ.hom₂ → T ∈ distTriang C) := by
  refine ⟨distinguished_coSpecial, ?_, ?_⟩
  · intro T₁ T₂
    let i₁ := sumInl T₁ T₂
    let i₂ := sumInr T₁ T₂
    let p₁ := sumFst T₁ T₂
    let p₂ := sumSnd T₁ T₂
    have hi₁ : i₁ ≫ p₁ = 𝟙 T₁ := by
      ext <;> simp [i₁, p₁, sumInl, sumFst]
    have hi₂ : i₂ ≫ p₂ = 𝟙 T₂ := by
      ext <;> simp [i₂, p₂, sumInr, sumSnd]
    have hs : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 (directSumTriangle T₁ T₂) := by
      ext <;> dsimp [i₁, i₂, p₁, p₂, sumInl, sumInr, sumFst, sumSnd,
        directSumTriangle, Triangle.mk] <;> exact biprod.total
    have : (rotate C).Additive := ⟨by intros; ext <;> simp [rotate]⟩
    have : (invRotate C).Additive := ⟨by intros; ext <;> simp [invRotate]⟩
    have he (K : Triangle C ⥤ Triangle C) [K.Additive] (W : C) (n : ℤ) :
        HomExact (K.obj (directSumTriangle T₁ T₂)) (shiftFunctor C n) W ↔
          HomExact (K.obj T₁) (shiftFunctor C n) W ∧
          HomExact (K.obj T₂) (shiftFunctor C n) W := by
      have h₁ : K.map i₁ ≫ K.map p₁ = 𝟙 _ := by
        rw [← K.map_comp, hi₁, K.map_id]
      have h₂ : K.map i₂ ≫ K.map p₂ = 𝟙 _ := by
        rw [← K.map_comp, hi₂, K.map_id]
      have hsum : K.map p₁ ≫ K.map i₁ + K.map p₂ ≫ K.map i₂ = 𝟙 _ := by
        rw [← K.map_comp, ← K.map_comp, ← K.map_add, hs, K.map_id]
      exact ⟨fun h ↦ ⟨homExact_retract _ _ h₁ _ W h,
        homExact_retract _ _ h₂ _ W h⟩,
        fun h ↦ homExact_sum _ _ _ _ hsum _ W h.1 h.2⟩
    constructor
    · intro h
      constructor <;> intro W n
      · exact ⟨((he (𝟭 _) W n).mp (h W n).1).1,
          ((he (rotate C) W n).mp (h W n).2.1).1,
          ((he (invRotate C) W n).mp (h W n).2.2).1⟩
      · exact ⟨((he (𝟭 _) W n).mp (h W n).1).2,
          ((he (rotate C) W n).mp (h W n).2.1).2,
          ((he (invRotate C) W n).mp (h W n).2.2).2⟩
    · rintro ⟨h₁, h₂⟩ W n
      exact ⟨(he (𝟭 _) W n).mpr ⟨(h₁ W n).1, (h₂ W n).1⟩,
        (he (rotate C) W n).mpr ⟨(h₁ W n).2.1, (h₂ W n).2.1⟩,
        (he (invRotate C) W n).mpr ⟨(h₁ W n).2.2, (h₂ W n).2.2⟩⟩
  · intro T T' hT hT' φ h₁ h₂
    let := h₁
    let := h₂
    let := comparison_isIso hT hT' φ
    let := Triangle.isIso_of_isIsos φ h₁ h₂ inferInstance
    exact isomorphic_distinguished T' hT' T (asIso φ)

end CategoryTheory.Pretriangulated
