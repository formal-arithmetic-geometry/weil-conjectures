/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Surjectivity of the signed horizontal column projection

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

/-- The actual column inclusion, extended by zero. -/
private noncomputable def extendedColumnInclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p : ℕ) (m : ℤ) :
    ((K.X p).extend ComplexShape.embeddingUpNat).X (m - (p : ℤ)) ⟶
      ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X m :=
  if hm : (p : ℤ) ≤ m then
    ((K.X p).extendXIso ComplexShape.embeddingUpNat
      (show ((m.toNat - p : ℕ) : ℤ) = m - (p : ℤ) by omega)).hom ≫
    coneHorizontalSummand K p m
  else 0

/-- The column projection retracts its actual inclusion. -/
private theorem extendedColumnInclusion_projection
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p : ℕ) (m : ℤ) :
    extendedColumnInclusion K p m ≫ horizontalExtendedProjection K p m = 𝟙 _ := by
  by_cases hm : (p : ℤ) ≤ m
  · have hm₀ : 0 ≤ m := by omega
    have hd : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (p, m.toNat - p) = m.toNat := by
      change p + (m.toNat - p) = m.toNat
      omega
    simp only [extendedColumnInclusion, dif_pos hm, horizontalExtendedProjection,
      coneHorizontalSummand, dif_pos hm₀, Category.assoc, Iso.inv_hom_id_assoc]
    rw [K.ιTotalOrZero_eq _ _ _ _ hd]
    simp [horizontalTotalProjection]
  · have hz := (K.X p).isZero_extend_X ComplexShape.embeddingUpNat
      (m - (p : ℤ)) (fun i hi ↦ by change (i : ℤ) = m - (p : ℤ) at hi; omega)
    exact hz.eq_of_src _ _

/-- The column source inclusion belongs to the horizontal tail. -/
private theorem columnSource_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (coneHorizontalStep f (p : ℤ) n).Factors
      (extendedColumnInclusion A p (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inlX
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat) (n + 1) n rfl) := by
  by_cases hn : (p : ℤ) ≤ n + 1
  · rw [extendedColumnInclusion, dif_pos hn, Category.assoc]
    apply Subobject.factors_of_factors_right
    refine Subobject.factors_of_le _ ?_
      (by simpa only [Category.id_comp] using imageSubobject_factors_comp_self _ (𝟙 _))
    apply le_trans le_sup_left
    apply Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_rfl⟩
  · simp [extendedColumnInclusion, hn, Subobject.factors_zero]

/-- The column target inclusion belongs to the horizontal tail. -/
private theorem columnTarget_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (coneHorizontalStep f (p : ℤ) n).Factors
      (extendedColumnInclusion B p n ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat)).f n) := by
  by_cases hn : (p : ℤ) ≤ n
  · rw [extendedColumnInclusion, dif_pos hn, Category.assoc]
    apply Subobject.factors_of_factors_right
    refine Subobject.factors_of_le _ ?_
      (by simpa only [Category.id_comp] using imageSubobject_factors_comp_self _ (𝟙 _))
    apply le_trans le_sup_right
    apply Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_rfl⟩
  · simp [extendedColumnInclusion, hn, Subobject.factors_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The signed column projection restricted to the horizontal tail is epimorphic.
Source: Stacks Project, Homology, Tag 012X, first-filtration column calculation;
existence node lem-sp-cone-horizontal-quotient-iso-exists, proof step 1.
(blueprint: lem-sp-cone-horizontal-projection-epi)

Proof: Insert the p-th source and target column summands in the total cone. Multiply the source
inclusion by (-1)^p, leave the target inclusion unchanged, and use their biproduct desc to obtain
a section. These inclusions factor through the p-tail because their images occur in its defining
finite supremum. The projection composed with the section is the identity: off-diagonal summands
project to zero and the source sign squares to one. In degrees below p-1 both column objects are
zero; in degree p-1 only the source summand occurs. Transport the factorization to the
representative F.step p using hF and its monic degreewise arrow. A map with a section is epi. -/
theorem coneHorizontal_projection_epi
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℕ) (n : ℤ) :
    Epi ((F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n) := by
  let q := HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  let c := HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat
  let k := n + -(p : ℤ)
  let ea := ((A.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
    (show n + 1 - (p : ℤ) = k + 1 by dsimp [k]; omega)
  let eb := ((B.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
    (show n - (p : ℤ) = k by dsimp [k]; omega)
  let a := ea.inv ≫ extendedColumnInclusion A p (n + 1) ≫
    HomologicalComplex.homotopyCofiber.inlX q (n + 1) n rfl
  let b := eb.inv ≫ extendedColumnInclusion B p n ≫
    (CochainComplex.mappingCone.inr q).f n
  let z : ℤ := (-1) ^ p
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod c k (k + 1) rfl
  let s := e.hom ≫ biprod.desc (z • a) b
  have hproj : coneHorizontalProjection f p n =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod q n (n + 1) rfl).hom ≫
        biprod.desc
          (z • (horizontalExtendedProjection A p (n + 1) ≫ ea.hom ≫
            HomologicalComplex.homotopyCofiber.inlX c (k + 1) k rfl))
          (horizontalExtendedProjection B p n ≫ eb.hom ≫
            (CochainComplex.mappingCone.inr c).f k) := rfl
  have ha : a ≫ coneHorizontalProjection f p n =
      z • HomologicalComplex.homotopyCofiber.inlX c (k + 1) k rfl := by
    rw [hproj]
    simp only [a, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc,
      biprod.inl_desc, Preadditive.comp_zsmul]
    rw [← Category.assoc (extendedColumnInclusion A p (n + 1)),
      extendedColumnInclusion_projection]
    simp
  have hb : b ≫ coneHorizontalProjection f p n =
      (CochainComplex.mappingCone.inr c).f k := by
    rw [hproj]
    change (eb.inv ≫ extendedColumnInclusion B p n ≫
      HomologicalComplex.homotopyCofiber.inrX q n) ≫ _ = _
    simp only [Category.assoc,
      HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc,
      biprod.inr_desc]
    rw [← Category.assoc (extendedColumnInclusion B p n),
      extendedColumnInclusion_projection]
    simp
  have hs : s ≫ coneHorizontalProjection f p n = 𝟙 _ := by
    have hz : z * z = 1 := by
      dsimp [z]
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    have hd : biprod.desc (z • a) b ≫ coneHorizontalProjection f p n =
        biprod.desc
          (HomologicalComplex.homotopyCofiber.inlX c (k + 1) k rfl)
          ((CochainComplex.mappingCone.inr c).f k) := by
      apply biprod.hom_ext'
      · simp only [biprod.inl_desc_assoc, biprod.inl_desc,
          Preadditive.zsmul_comp, ha, smul_smul, hz, one_smul]
      · simp only [biprod.inr_desc_assoc, biprod.inr_desc, hb]
    have hd' : biprod.desc
        (HomologicalComplex.homotopyCofiber.inlX c (k + 1) k rfl)
        ((CochainComplex.mappingCone.inr c).f k) = e.inv := by
      apply biprod.hom_ext'
      · simp [e]
      · simpa [e] using (show (CochainComplex.mappingCone.inr c).f k =
          HomologicalComplex.homotopyCofiber.inrX c k from rfl)
    change (e.hom ≫ biprod.desc (z • a) b) ≫ _ = _
    rw [Category.assoc, hd, hd']
    exact e.hom_inv_id
  have hsa : (coneHorizontalStep f (p : ℤ) n).Factors a :=
    Subobject.factors_of_factors_right ea.inv (columnSource_factors f p n)
  have hsb : (coneHorizontalStep f (p : ℤ) n).Factors b :=
    Subobject.factors_of_factors_right eb.inv (columnTarget_factors f p n)
  have hsz : (coneHorizontalStep f (p : ℤ) n).Factors (z • a) := by
    rw [← Subobject.factorThru_arrow _ _ hsa, ← Preadditive.zsmul_comp]
    exact Subobject.factors_comp_arrow _
  have hsf : (coneHorizontalStep f (p : ℤ) n).Factors s := by
    dsimp only [s]
    apply Subobject.factors_of_factors_right
    rw [biprod.desc_eq]
    apply Subobject.factors_add
    · exact Subobject.factors_of_factors_right biprod.fst hsz
    · exact Subobject.factors_of_factors_right biprod.snd hsb
  have hsm : (Subobject.mk ((F.step (p : ℤ)).arrow.f n)).Factors s := by
    rw [← imageSubobject_mono, ← DecreasingFiltration.complexStep, hF]
    exact hsf
  obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff _ _).1 hsm
  change t ≫ (F.step (p : ℤ)).arrow.f n = s at ht
  have hsec : t ≫ ((F.step (p : ℤ)).arrow.f n ≫
      coneHorizontalProjection f p n) = 𝟙 _ := by
    rw [← Category.assoc, ht]
    exact hs
  exact (SplitEpi.mk t hsec).epi

end HomologicalComplex₂
