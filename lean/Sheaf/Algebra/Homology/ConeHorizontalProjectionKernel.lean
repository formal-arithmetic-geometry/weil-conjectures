/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Kernel of the signed horizontal column projection

Source: Stacks Project, Homology, Tag 012X, first-filtration formula before
Lemma 12.25.1 (label lemma-double-complex), with the cone refinement in
lem-sp-cone-horizontal-quotient-iso-exists, proof step 1.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- Inclusion of an extended column into the extended total object. -/
private noncomputable def kernelColumnInclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p : ℕ) (m : ℤ) :
    ((K.X p).extend ComplexShape.embeddingUpNat).X (m - (p : ℤ)) ⟶
      ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X m :=
  if hm : (p : ℤ) ≤ m then
    ((K.X p).extendXIso ComplexShape.embeddingUpNat
      (show ((m.toNat - p : ℕ) : ℤ) = m - (p : ℤ) by omega)).hom ≫
    coneHorizontalSummand K p m
  else 0

/-- A summand outside the chosen column projects to zero. -/
private theorem summand_projection_zero
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p h : ℕ) (m : ℤ) (hh : h ≠ p) :
    coneHorizontalSummand K h m ≫ horizontalExtendedProjection K p m = 0 := by
  by_cases hm : (p : ℤ) ≤ m
  · have hm₀ : 0 ≤ m := by omega
    by_cases hd : h ≤ m.toNat
    · have he : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (h, m.toNat - h) = m.toNat := by change h + (m.toNat - h) = m.toNat; omega
      simp only [coneHorizontalSummand, dif_pos hm₀, horizontalExtendedProjection,
        dif_pos hm, Category.assoc, Iso.inv_hom_id_assoc]
      rw [K.ιTotalOrZero_eq _ _ _ _ he]
      simp [horizontalTotalProjection, hh]
    · have hz : K.ιTotalOrZero (ComplexShape.up ℕ) h (m.toNat - h) m.toNat = 0 :=
        K.ιTotalOrZero_eq_zero _ _ _ _ (by change h + (m.toNat - h) ≠ m.toNat; omega)
      simp [coneHorizontalSummand, hz]
  · simp [horizontalExtendedProjection, hm]

/-- Projection followed by column inclusion fixes a generator in that column. -/
private theorem summand_projection_inclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p : ℕ) (m : ℤ) :
    coneHorizontalSummand K p m ≫ horizontalExtendedProjection K p m ≫
      kernelColumnInclusion K p m = coneHorizontalSummand K p m := by
  by_cases hm : (p : ℤ) ≤ m
  · have hm₀ : 0 ≤ m := by omega
    have he : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (p, m.toNat - p) = m.toNat := by change p + (m.toNat - p) = m.toNat; omega
    simp only [coneHorizontalSummand, dif_pos hm₀, horizontalExtendedProjection,
      kernelColumnInclusion, dif_pos hm, Category.assoc, Iso.inv_hom_id_assoc]
    rw [K.ιTotalOrZero_eq _ _ _ _ he]
    simp [horizontalTotalProjection]
  · have hz : coneHorizontalSummand K p m = 0 := by
      by_cases hm₀ : 0 ≤ m
      · have hd : K.ιTotalOrZero (ComplexShape.up ℕ) p (m.toNat - p) m.toNat = 0 :=
          K.ιTotalOrZero_eq_zero _ _ _ _
            (by change p + (m.toNat - p) ≠ m.toNat; omega)
        simp [coneHorizontalSummand, hm₀, hd]
      · simp [coneHorizontalSummand, hm₀]
    simp [hz]

/-- A source generator with the stated index belongs to the tail. -/
private theorem kernelSource_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (r n : ℤ) (h : ℕ) (hr : r ≤ (h : ℤ)) :
    (coneHorizontalStep f r n).Factors (coneHorizontalSummand A h (n + 1) ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat) (n + 1) n rfl) := by
  by_cases hn : 0 ≤ n + 1
  · by_cases hh : h ≤ (n + 1).toNat
    · apply Subobject.factors_of_le _ (le_trans le_sup_left
        (Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n) (by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hr⟩)))
      simpa only [Category.id_comp] using imageSubobject_factors_comp_self _ (𝟙 _)
    · have hz : A.ιTotalOrZero (ComplexShape.up ℕ) h ((n + 1).toNat - h)
          (n + 1).toNat = 0 := A.ιTotalOrZero_eq_zero _ _ _ _
            (by change h + ((n + 1).toNat - h) ≠ (n + 1).toNat; omega)
      simp [coneHorizontalSummand, hz, Subobject.factors_zero]
  · simp [coneHorizontalSummand, hn, Subobject.factors_zero]

/-- A target generator with the stated index belongs to the tail. -/
private theorem kernelTarget_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (r n : ℤ) (h : ℕ) (hr : r ≤ (h : ℤ)) :
    (coneHorizontalStep f r n).Factors (coneHorizontalSummand B h n ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat)).f n) := by
  by_cases hn : 0 ≤ n
  · by_cases hh : h ≤ n.toNat
    · apply Subobject.factors_of_le _ (le_trans le_sup_right
        (Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n) (by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hr⟩)))
      simpa only [Category.id_comp] using imageSubobject_factors_comp_self _ (𝟙 _)
    · have hz : B.ιTotalOrZero (ComplexShape.up ℕ) h (n.toNat - h) n.toNat = 0 :=
          B.ιTotalOrZero_eq_zero _ _ _ _ (by change h + (n.toNat - h) ≠ n.toNat; omega)
      simp [coneHorizontalSummand, hz, Subobject.factors_zero]
  · simp [coneHorizontalSummand, hn, Subobject.factors_zero]

/-- Test factorization of a tail map on its source and target generators. -/
private theorem kernelTail_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (r n : ℤ) {Y : C}
    (d : (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).X n ⟶ Y) (Q : Subobject Y)
    (hs : ∀ h : ℕ, r ≤ (h : ℤ) → Q.Factors
      ((coneHorizontalSummand A h (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inlX
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat) (n + 1) n rfl) ≫ d))
    (ht : ∀ h : ℕ, r ≤ (h : ℤ) → Q.Factors
      ((coneHorizontalSummand B h n ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat)).f n) ≫ d)) :
    Q.Factors ((coneHorizontalStep f r n).arrow ≫ d) := by
  let P := (Subobject.pullback d).obj Q
  have hle : coneHorizontalStep f r n ≤ P := by
    apply Finset.sup_le
    intro h hh
    have hr := (Finset.mem_filter.mp hh).2
    apply sup_le
    · have hf := pullback_factors d Q _ (hs h hr)
      exact imageSubobject_le _ (P.factorThru _ hf) (Subobject.factorThru_arrow _ _ _)
    · have hf := pullback_factors d Q _ (ht h hr)
      exact imageSubobject_le _ (P.factorThru _ hf) (Subobject.factorThru_arrow _ _ _)
  exact (pullback_factors_iff d Q _).1
    (Subobject.factors_of_le _ hle (Subobject.factors_self _))

/-- Insert the column in the cone, with the same source sign as the projection. -/
private noncomputable def kernelColumnSection
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).X n ⟶
    (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).X n :=
  let q := HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  let c := HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat
  let k := n + -(p : ℤ)
  (HomologicalComplex.homotopyCofiber.XIsoBiprod c k (k + 1) rfl).hom ≫
    biprod.desc
      (((-1 : ℤ) ^ p) •
        ((((A.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
          (show n + 1 - (p : ℤ) = k + 1 by dsimp [k]; omega)).inv ≫
        kernelColumnInclusion A p (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inlX q (n + 1) n rfl))
      ((((B.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show n - (p : ℤ) = k by dsimp [k]; omega)).inv ≫
        kernelColumnInclusion B p n ≫ (CochainComplex.mappingCone.inr q).f n)

/-- A source generator outside column p is killed by the cone projection. -/
private theorem kernelSource_projection_zero
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p h : ℕ) (n : ℤ) (hh : h ≠ p) :
    (coneHorizontalSummand A h (n + 1) ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat) (n + 1) n rfl) ≫
      coneHorizontalProjection f p n = 0 := by
  simp only [coneHorizontalProjection, Category.assoc,
    HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc,
    biprod.inl_desc, Preadditive.comp_zsmul]
  rw [← Category.assoc (coneHorizontalSummand A h (n + 1)),
    summand_projection_zero A p h (n + 1) hh]
  simp

/-- A target generator outside column p is killed by the cone projection. -/
private theorem kernelTarget_projection_zero
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p h : ℕ) (n : ℤ) (hh : h ≠ p) :
    (coneHorizontalSummand B h n ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat)).f n) ≫ coneHorizontalProjection f p n = 0 := by
  change (coneHorizontalSummand B h n ≫
    HomologicalComplex.homotopyCofiber.inrX _ n) ≫ _ = _
  simp only [coneHorizontalProjection, Category.assoc,
    HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc, biprod.inr_desc]
  rw [← Category.assoc (coneHorizontalSummand B h n),
    summand_projection_zero B p h n hh]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The column part of a source generator reconstructs that generator. -/
private theorem kernelSource_reconstruction
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (coneHorizontalSummand A p (n + 1) ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat) (n + 1) n rfl) ≫
      coneHorizontalProjection f p n ≫ kernelColumnSection f p n =
    coneHorizontalSummand A p (n + 1) ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat) (n + 1) n rfl := by
  have hz : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  simp only [coneHorizontalProjection, kernelColumnSection, Category.assoc,
    HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc,
    biprod.inl_desc_assoc, biprod.inl_desc, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    smul_smul, hz, one_smul, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ HomologicalComplex.homotopyCofiber.inlX
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat) (n + 1) n rfl)
    (summand_projection_inclusion A p (n + 1))

set_option backward.isDefEq.respectTransparency false in
/-- The column part of a target generator reconstructs that generator. -/
private theorem kernelTarget_reconstruction
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (coneHorizontalSummand B p n ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat)).f n) ≫
      coneHorizontalProjection f p n ≫ kernelColumnSection f p n =
    coneHorizontalSummand B p n ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat)).f n := by
  change (coneHorizontalSummand B p n ≫
    HomologicalComplex.homotopyCofiber.inrX _ n) ≫ _ ≫ _ = _
  simp only [coneHorizontalProjection, kernelColumnSection,
    CochainComplex.mappingCone.inr, HomologicalComplex.homotopyCofiber.inr,
    Category.assoc,
    HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc,
    biprod.inr_desc_assoc, biprod.inr_desc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ HomologicalComplex.homotopyCofiber.inrX
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat) n) (summand_projection_inclusion B p n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The next horizontal tail is exactly the kernel of the restricted signed projection.
Source: Stacks Project, Homology, Tag 012X, first-filtration column calculation;
existence node lem-sp-cone-horizontal-quotient-iso-exists, proof step 1.
(blueprint: lem-sp-cone-horizontal-projection-kernel)

Proof: In each degree the horizontal tail is the sum of the diagonal source and target summands
with horizontal index at least p. In the biproduct coordinates the signed projection is (-1)^p
times the source coordinate at p and the target coordinate at p. Both coefficients are invertible.
Its kernel is therefore precisely the sum of coordinates with index strictly greater than p, which
is the next tail. The inclusion of F.step (p+1) into F.step p is monic in each degree and hF
identifies its ambient image with that next tail. Pulling this equality back along the monic arrow
of F.step p gives the stated kernel equality. For n<p-1 the column object and p-tail are zero; at
n=p-1 only the source coordinate is present, so the same argument applies. -/
theorem coneHorizontal_projection_kernel
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℕ) (n : ℤ) :
    imageSubobject ((Subobject.ofLE (F.step ((p : ℤ) + 1))
      (F.step (p : ℤ)) (F.antitone_step (by omega))).f n) =
      kernelSubobject ((F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n) := by
  let a := (F.step (p : ℤ)).arrow.f n
  let b := (F.step ((p : ℤ) + 1)).arrow.f n
  let i := (Subobject.ofLE (F.step ((p : ℤ) + 1)) (F.step (p : ℤ))
    (F.antitone_step (by omega))).f n
  let g := coneHorizontalProjection f p n
  let s := kernelColumnSection f p n
  let Q := coneHorizontalStep f ((p : ℤ) + 1) n
  have hi : i ≫ a = b := by
    dsimp only [i, a, b]
    exact HomologicalComplex.congr_hom (Subobject.ofLE_arrow (F.antitone_step (by omega))) n
  have ha : Subobject.mk a = coneHorizontalStep f (p : ℤ) n := by
    rw [← imageSubobject_mono a]
    exact hF (p : ℤ) n
  have hb : Subobject.mk b = Q := by
    rw [← imageSubobject_mono b]
    exact hF ((p : ℤ) + 1) n
  have hzero : Q.arrow ≫ g = 0 := by
    have hle : Q ≤ kernelSubobject g := by
      apply Finset.sup_le
      intro h hh
      have hp : h ≠ p := by
        have := (Finset.mem_filter.mp hh).2
        omega
      apply sup_le
      · exact le_kernelSubobject g _
          (imageSubobject_arrow_comp_eq_zero (kernelSource_projection_zero f p h n hp))
      · exact le_kernelSubobject g _
          (imageSubobject_arrow_comp_eq_zero (kernelTarget_projection_zero f p h n hp))
    exact (kernelSubobject_factors_iff g Q.arrow).1
      (Subobject.factors_of_le _ hle (Subobject.factors_self Q))
  have hbg : b ≫ g = 0 := by
    have hf : Q.Factors b := by
      rw [← hb]
      exact (Subobject.mk_factors_iff b b).2 ⟨𝟙 _, by simp⟩
    rw [← Subobject.factorThru_arrow Q b hf, Category.assoc, hzero, comp_zero]
  have hdefect : Q.Factors
      ((coneHorizontalStep f (p : ℤ) n).arrow ≫ (𝟙 _ - g ≫ s)) := by
    apply kernelTail_factors
    · intro h hh
      by_cases he : h = p
      · subst h
        simp only [Preadditive.comp_sub, kernelSource_reconstruction, g, s]
        let t := coneHorizontalSummand A p (n + 1) ≫
          HomologicalComplex.homotopyCofiber.inlX
            (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
              ComplexShape.embeddingUpNat) (n + 1) n rfl
        change Q.Factors (t ≫ 𝟙 _ - t)
        simp only [Category.comp_id, sub_self, Subobject.factors_zero]
      · have hp : (p : ℤ) + 1 ≤ (h : ℤ) := by omega
        simp only [Preadditive.comp_sub, ← Category.assoc,
          kernelSource_projection_zero f p h n he, zero_comp, sub_zero, g, s]
        let t := coneHorizontalSummand A h (n + 1) ≫
          HomologicalComplex.homotopyCofiber.inlX
            (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
              ComplexShape.embeddingUpNat) (n + 1) n rfl
        change Q.Factors (t ≫ 𝟙 _)
        rw [Category.comp_id]
        exact kernelSource_factors f ((p : ℤ) + 1) n h hp
    · intro h hh
      by_cases he : h = p
      · subst h
        simp only [Preadditive.comp_sub, Category.comp_id,
          kernelTarget_reconstruction, sub_self, Subobject.factors_zero, g, s]
      · have hp : (p : ℤ) + 1 ≤ (h : ℤ) := by omega
        simpa only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
          kernelTarget_projection_zero f p h n he, zero_comp, sub_zero, g, s] using
          kernelTarget_factors f ((p : ℤ) + 1) n h hp
  change imageSubobject i = kernelSubobject (a ≫ g)
  apply le_antisymm
  · apply le_kernelSubobject (a ≫ g)
    apply imageSubobject_arrow_comp_eq_zero
    simpa only [← Category.assoc, hi] using hbg
  · let R := kernelSubobject (a ≫ g)
    let x := R.arrow ≫ a
    have hx : Q.Factors x := by
      have hax : (coneHorizontalStep f (p : ℤ) n).Factors a := by
        rw [← ha]
        exact (Subobject.mk_factors_iff a a).2 ⟨𝟙 _, by simp⟩
      have hx' := Subobject.factors_of_factors_right (R.arrow ≫
        (coneHorizontalStep f (p : ℤ) n).factorThru a hax) hdefect
      have hxg : x ≫ g = 0 := by
        dsimp only [x, R]
        simp only [Category.assoc, kernelSubobject_arrow_comp]
      have hx'' : Q.Factors (x ≫ (𝟙 _ - g ≫ s)) := by
        simpa only [Category.assoc, Subobject.factorThru_arrow_assoc, x] using hx'
      simpa only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
        hxg, zero_comp, sub_zero] using hx''
    rw [← hb] at hx
    obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff b x).1 hx
    change t ≫ b = x at ht
    have hti : t ≫ i = R.arrow := by
      apply (cancel_mono a).1
      simpa only [Category.assoc, hi, x] using ht
    rw [imageSubobject_mono i]
    exact Subobject.le_mk_of_comm t hti

end HomologicalComplex₂
