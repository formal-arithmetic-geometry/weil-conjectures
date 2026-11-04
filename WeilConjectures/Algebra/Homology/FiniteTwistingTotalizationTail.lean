/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationMatrix

/-! # Tail subcomplexes of a finite twisting totalization

Given matrix data `X` for a finite twisting family `D`, the tail of weight `r` is the
direct sum of the summands of weight at least `r`.  Since the differential of `X.P` is
upper triangular, the tails are subcomplexes, and they form a decreasing filtration
whose graded pieces are the complexes `D.G p`.

## Main definitions

- `CochainComplex.FiniteTwistingMatrixData.tailComplex`: the tail complex of weight `r`.
- `CochainComplex.FiniteTwistingMatrixData.tailι`: its inclusion into `X.P`.
- `CochainComplex.FiniteTwistingMatrixData.tailFiltration`: the tail filtration of `X.P`.
- `CochainComplex.FiniteTwistingMatrixData.tailGradedπ`: the projection of the tail of
  weight `p` onto `D.G p`.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

/-- In a biproduct indexed by a subtype, the composite of an inclusion and a projection agrees
with the corresponding composite in the biproduct indexed by the ambient type. -/
lemma CategoryTheory.Limits.biproduct.ι_π_subtype {𝒞 : Type*} [Category 𝒞]
    [HasZeroMorphisms 𝒞] {ι : Type*} (g : ι → 𝒞) (P : ι → Prop)
    [HasBiproduct g] [HasBiproduct fun q : {q : ι // P q} ↦ g q.val] (q t : {q : ι // P q}) :
    biproduct.ι (fun q : {q : ι // P q} ↦ g q.val) q ≫
        biproduct.π (fun q : {q : ι // P q} ↦ g q.val) t =
      biproduct.ι g q.val ≫ biproduct.π g t.val := by
  classical
  by_cases h : q = t
  · subst h
    simp
  · rw [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ (fun e ↦ h (Subtype.ext e))]

namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

namespace FiniteTwistingFamily

variable (D : FiniteTwistingFamily R a b)

/-- The inclusion of the summands of weight at least `r` into the full direct sum. -/
noncomputable def tailIncl (r n : ℤ) :
    (⨁ fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n) ⟶
      ⨁ fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n :=
  biproduct.desc fun q ↦ biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q.val

/-- The projection of the full direct sum onto the summands of weight at least `r`. -/
noncomputable def tailProj (r n : ℤ) :
    (⨁ fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) ⟶
      ⨁ fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n :=
  biproduct.lift fun q ↦ biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q.val

@[reassoc (attr := simp)]
lemma ι_tailIncl (r n : ℤ) (q : {q : ↥(Finset.Icc a b) // r ≤ q.val}) :
    biproduct.ι (fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n) q ≫
        D.tailIncl r n =
      biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q.val :=
  biproduct.ι_desc _ _

@[reassoc (attr := simp)]
lemma tailProj_π (r n : ℤ) (q : {q : ↥(Finset.Icc a b) // r ≤ q.val}) :
    D.tailProj r n ≫
        biproduct.π (fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n) q =
      biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q.val :=
  biproduct.lift_π _ _

@[reassoc (attr := simp)]
lemma tailIncl_tailProj (r n : ℤ) : D.tailIncl r n ≫ D.tailProj r n = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun q ↦ biproduct.hom_ext _ _ fun t ↦ ?_
  rw [Category.assoc, Category.assoc, ι_tailIncl_assoc, tailProj_π, Category.comp_id]
  exact (biproduct.ι_π_subtype (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) _ q t).symm

/-- Projecting a summand of weight at least `r` from the tail of weight `r`. -/
@[reassoc]
lemma tailIncl_π_of_le (r n : ℤ) (t : ↥(Finset.Icc a b)) (h : r ≤ t.val) :
    D.tailIncl r n ≫ biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) t =
      biproduct.π (fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n)
        ⟨t, h⟩ := by
  refine biproduct.hom_ext' _ _ fun q ↦ ?_
  rw [ι_tailIncl_assoc]
  exact (biproduct.ι_π_subtype (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) _ q ⟨t, h⟩).symm

/-- Projecting a summand of weight less than `r` from the tail of weight `r` gives zero. -/
@[reassoc]
lemma tailIncl_π_of_not_le (r n : ℤ) (t : ↥(Finset.Icc a b)) (h : ¬ r ≤ t.val) :
    D.tailIncl r n ≫ biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) t = 0 := by
  refine biproduct.hom_ext' _ _ fun q ↦ ?_
  rw [ι_tailIncl_assoc, comp_zero,
    biproduct.ι_π_ne _ (fun e ↦ h (by rw [← e]; exact q.property))]

/-- Including a summand of weight at least `r` and then projecting to the tail. -/
@[reassoc]
lemma ι_tailProj_of_le (r n : ℤ) (q : ↥(Finset.Icc a b)) (h : r ≤ q.val) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q ≫ D.tailProj r n =
      biproduct.ι (fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n)
        ⟨q, h⟩ := by
  refine biproduct.hom_ext _ _ fun t ↦ ?_
  rw [Category.assoc, tailProj_π]
  exact (biproduct.ι_π_subtype (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) _ ⟨q, h⟩ t).symm

/-- The idempotent `tailProj ≫ tailIncl` followed by a projection. -/
@[reassoc]
lemma tailProj_tailIncl_π (r n : ℤ) (t : ↥(Finset.Icc a b)) :
    D.tailProj r n ≫ D.tailIncl r n ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) t =
      if r ≤ t.val then biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) t else 0 := by
  split_ifs with h
  · rw [tailIncl_π_of_le _ _ _ _ h, tailProj_π]
  · rw [tailIncl_π_of_not_le _ _ _ _ h, comp_zero]

/-- A smaller tail factors through a larger one. -/
@[reassoc (attr := simp)]
lemma tailIncl_tailProj_tailIncl {r r' : ℤ} (h : r ≤ r') (n : ℤ) :
    D.tailIncl r' n ≫ D.tailProj r n ≫ D.tailIncl r n = D.tailIncl r' n := by
  refine biproduct.hom_ext' _ _ fun q ↦ ?_
  rw [ι_tailIncl_assoc, ι_tailProj_of_le_assoc _ _ _ _ (h.trans q.property), ι_tailIncl,
    ι_tailIncl]

/-- The tail of weight `r ≤ a` is everything. -/
lemma tailProj_tailIncl_of_le {r : ℤ} (h : r ≤ a) (n : ℤ) :
    D.tailProj r n ≫ D.tailIncl r n = 𝟙 _ := by
  refine biproduct.hom_ext _ _ fun t ↦ ?_
  rw [Category.assoc, tailProj_tailIncl_π, if_pos (h.trans (Finset.mem_Icc.mp t.property).1),
    Category.id_comp]

/-- The tail of weight `r > b` is zero. -/
lemma tailIncl_eq_zero {r : ℤ} (h : b < r) (n : ℤ) : D.tailIncl r n = 0 :=
  biproduct.hom_ext' _ _ fun q ↦
    absurd ((Finset.mem_Icc.mp q.val.property).2.trans_lt h) (not_lt.mpr q.property)

/-- Retracting a tail onto a smaller tail. -/
lemma tailIncl_tailProj_tailIncl_tailProj {r r' : ℤ} (h : r ≤ r') (n : ℤ) :
    (D.tailIncl r' n ≫ D.tailProj r n) ≫ D.tailIncl r n ≫ D.tailProj r' n = 𝟙 _ := by
  rw [Category.assoc, D.tailIncl_tailProj_tailIncl_assoc h, tailIncl_tailProj]

/-- The tail of weight `p` splits as the tail of weight `p + 1` plus the summand of
weight `p`. -/
lemma tailSplitting_id (p : ↥(Finset.Icc a b)) (n : ℤ) :
    (D.tailIncl p.val n ≫ D.tailProj (p.val + 1) n) ≫ D.tailIncl (p.val + 1) n ≫
        D.tailProj p.val n +
      biproduct.π (fun q : {q : ↥(Finset.Icc a b) // p.val ≤ q.val} ↦ (D.G q.val).X n)
          ⟨p, le_rfl⟩ ≫
        biproduct.ι (fun q : {q : ↥(Finset.Icc a b) // p.val ≤ q.val} ↦ (D.G q.val).X n)
          ⟨p, le_rfl⟩ = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun q ↦ biproduct.hom_ext _ _ fun t ↦ ?_
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc, ι_tailIncl_assoc,
    tailProj_π, tailProj_tailIncl_π, Category.id_comp]
  by_cases ht : p.val + 1 ≤ t.val.val
  · have hne : (⟨p, le_rfl⟩ : {q : ↥(Finset.Icc a b) // p.val ≤ q.val}) ≠ t := by
      rintro rfl
      simp at ht
    rw [if_pos ht, biproduct.ι_π_ne _ hne, comp_zero, comp_zero, add_zero]
    exact (biproduct.ι_π_subtype (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) _ q t).symm
  · obtain rfl : t = ⟨p, le_rfl⟩ :=
      Subtype.ext (Subtype.ext (le_antisymm (Int.lt_add_one_iff.mp (not_le.mp ht)) t.property))
    rw [if_neg ht, comp_zero, zero_add, biproduct.ι_π_self, Category.comp_id]

end FiniteTwistingFamily

namespace FiniteTwistingMatrixData

variable {D : FiniteTwistingFamily R a b} (X : FiniteTwistingMatrixData D)

/-- The differential of `X.P` transported to the direct-sum coordinates. -/
noncomputable def coordinateDifferential (n m : ℤ) :
    (⨁ fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) ⟶
      ⨁ fun q : ↥(Finset.Icc a b) ↦ (D.G q).X m :=
  (X.coordinates n).inv ≫ X.P.d n m ≫ (X.coordinates m).hom

/-- In coordinates, the differential of `X.P` is the twisting matrix. -/
lemma coordinateDifferential_succ (n : ℤ) :
    X.coordinateDifferential n (n + 1) = finiteTwistingMatrix D n := by
  refine biproduct.hom_ext' _ _ fun p ↦ ?_
  simp only [coordinateDifferential, reassoc_of% (X.differential p n), ι_finiteTwistingMatrix,
    Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

lemma coordinateDifferential_eq_zero {n m : ℤ} (h : n + 1 ≠ m) :
    X.coordinateDifferential n m = 0 := by
  rw [coordinateDifferential, X.P.shape n m h, zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma coordinateDifferential_comp (n m k : ℤ) :
    X.coordinateDifferential n m ≫ X.coordinateDifferential m k = 0 := by
  simp [coordinateDifferential]

/-- The differential never lowers the weight. -/
lemma ι_coordinateDifferential_π_of_lt (n m : ℤ) (q t : ↥(Finset.Icc a b))
    (h : t.val < q.val) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q ≫
      X.coordinateDifferential n m ≫
      biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X m) t = 0 := by
  by_cases hnm : n + 1 = m
  · subst hnm
    simp only [coordinateDifferential_succ, ι_finiteTwistingMatrix_π,
      dif_neg (fun e : q = t ↦ h.ne' (congrArg Subtype.val e)), dif_neg (not_lt.mpr h.le),
      add_zero]
  · simp only [X.coordinateDifferential_eq_zero hnm, zero_comp, comp_zero]

/-- The diagonal entries of the differential are the differentials of the summands. -/
lemma ι_coordinateDifferential_π_self (n m : ℤ) (p : ↥(Finset.Icc a b)) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
      X.coordinateDifferential n m ≫
      biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X m) p = (D.G p).d n m := by
  by_cases hnm : n + 1 = m
  · subst hnm
    simp only [coordinateDifferential_succ, ι_finiteTwistingMatrix_π, dite_true,
      dif_neg (lt_irrefl p.val), eqToHom_refl, Category.comp_id, add_zero]
  · simp only [X.coordinateDifferential_eq_zero hnm, zero_comp, comp_zero,
      (D.G p).shape n m hnm]

/-- The differential preserves every tail. -/
@[reassoc]
lemma tailIncl_coordinateDifferential_tailProj_tailIncl (r n m : ℤ) :
    D.tailIncl r n ≫ X.coordinateDifferential n m ≫ D.tailProj r m ≫ D.tailIncl r m =
      D.tailIncl r n ≫ X.coordinateDifferential n m := by
  refine biproduct.hom_ext' _ _ fun q ↦ biproduct.hom_ext _ _ fun t ↦ ?_
  simp only [Category.assoc, FiniteTwistingFamily.ι_tailIncl_assoc,
    FiniteTwistingFamily.tailProj_tailIncl_π]
  split_ifs with h
  · rfl
  · rw [comp_zero, comp_zero,
      X.ι_coordinateDifferential_π_of_lt n m q.val t (lt_of_lt_of_le (not_le.mp h) q.property)]

/-- The tail subcomplex of weight `r`: the summands of weight at least `r`. -/
noncomputable def tailComplex (r : ℤ) : CochainComplex (finiteTwistingModule D) ℤ where
  X n := ⨁ fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n
  d n m := D.tailIncl r n ≫ X.coordinateDifferential n m ≫ D.tailProj r m
  shape n m h := by
    rw [X.coordinateDifferential_eq_zero h, zero_comp, comp_zero]
  d_comp_d' n m k _ _ := by
    simp only [Category.assoc]
    rw [X.tailIncl_coordinateDifferential_tailProj_tailIncl_assoc,
      coordinateDifferential_comp_assoc, zero_comp, comp_zero]

lemma tailComplex_d (r n m : ℤ) :
    (X.tailComplex r).d n m =
      D.tailIncl r n ≫ X.coordinateDifferential n m ≫ D.tailProj r m :=
  rfl

/-- The inclusion of the tail of weight `r` into `X.P`. -/
noncomputable def tailι (r : ℤ) : X.tailComplex r ⟶ X.P where
  f n := D.tailIncl r n ≫ (X.coordinates n).inv
  comm' n m _ := by
    rw [tailComplex_d]
    simp only [Category.assoc]
    rw [X.tailIncl_coordinateDifferential_tailProj_tailIncl_assoc, coordinateDifferential]
    simp

lemma tailι_f (r n : ℤ) : (X.tailι r).f n = D.tailIncl r n ≫ (X.coordinates n).inv :=
  rfl

/-- The coordinate projection retracts the tail inclusion in each degree. -/
@[reassoc (attr := simp)]
lemma tailι_f_retraction (r n : ℤ) :
    (X.tailι r).f n ≫ (X.coordinates n).hom ≫ D.tailProj r n =
      𝟙 (⨁ fun q : {q : ↥(Finset.Icc a b) // r ≤ q.val} ↦ (D.G q.val).X n) := by
  simp [tailι_f]

instance (r : ℤ) : Mono (X.tailι r) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦ mono_of_mono_fac (X.tailι_f_retraction r n)

/-- The inclusion of the tail of weight `r'` into the tail of weight `r ≤ r'`. -/
noncomputable def tailMap {r r' : ℤ} (h : r ≤ r') : X.tailComplex r' ⟶ X.tailComplex r where
  f n := D.tailIncl r' n ≫ D.tailProj r n
  comm' n m _ := by
    rw [tailComplex_d, tailComplex_d]
    simp only [Category.assoc]
    rw [D.tailIncl_tailProj_tailIncl_assoc h,
      X.tailIncl_coordinateDifferential_tailProj_tailIncl_assoc]

lemma tailMap_f {r r' : ℤ} (h : r ≤ r') (n : ℤ) :
    (X.tailMap h).f n = D.tailIncl r' n ≫ D.tailProj r n :=
  rfl

@[reassoc (attr := simp)]
lemma tailMap_comp_tailι {r r' : ℤ} (h : r ≤ r') :
    X.tailMap h ≫ X.tailι r = X.tailι r' := by
  ext n
  simp only [HomologicalComplex.comp_f, tailMap_f, tailι_f, Category.assoc,
    D.tailIncl_tailProj_tailIncl_assoc h]

/-- The tail filtration of `X.P`: its step of weight `r` is the tail subcomplex. -/
noncomputable def tailFiltration : DecreasingFiltration X.P where
  F r := Subobject.mk (X.tailι r)
  F_succ_le _ := Subobject.mk_le_mk_of_comm (X.tailMap (Int.le_add_one le_rfl))
    (X.tailMap_comp_tailι _)

lemma tailFiltration_F (r : ℤ) : X.tailFiltration.F r = Subobject.mk (X.tailι r) :=
  rfl

/-- The projection of the tail of weight `p` onto its lowest summand `D.G p`. -/
noncomputable def tailGradedπ (p : ↥(Finset.Icc a b)) : X.tailComplex p.val ⟶ D.G p where
  f n := biproduct.π (fun q : {q : ↥(Finset.Icc a b) // p.val ≤ q.val} ↦ (D.G q.val).X n)
    ⟨p, le_rfl⟩
  comm' n m _ := by
    rw [tailComplex_d]
    refine biproduct.hom_ext' _ _ fun q ↦ ?_
    simp only [Category.assoc, FiniteTwistingFamily.ι_tailIncl_assoc,
      FiniteTwistingFamily.tailProj_π]
    obtain ⟨q, hq⟩ := q
    rcases hq.lt_or_eq with hlt | heq
    · rw [biproduct.ι_π_ne_assoc _ (fun e ↦ hlt.ne' (congrArg (fun x ↦ x.val.val) e)),
        zero_comp, X.ι_coordinateDifferential_π_of_lt n m q p hlt]
    · obtain rfl : q = p := Subtype.ext heq.symm
      rw [biproduct.ι_π_self_assoc, X.ι_coordinateDifferential_π_self]

lemma tailGradedπ_f (p : ↥(Finset.Icc a b)) (n : ℤ) :
    (X.tailGradedπ p).f n =
      biproduct.π (fun q : {q : ↥(Finset.Icc a b) // p.val ≤ q.val} ↦ (D.G q.val).X n)
        ⟨p, le_rfl⟩ :=
  rfl

@[reassoc (attr := simp)]
lemma tailMap_comp_tailGradedπ (p : ↥(Finset.Icc a b)) :
    X.tailMap (Int.le_add_one le_rfl) ≫ X.tailGradedπ p = 0 := by
  ext n
  rw [HomologicalComplex.comp_f, tailMap_f, tailGradedπ_f, Category.assoc,
    FiniteTwistingFamily.tailProj_π, FiniteTwistingFamily.tailIncl_π_of_not_le _ _ _ _
      (by simp), HomologicalComplex.zero_f]

/-- The short complex `tail (p + 1) ⟶ tail p ⟶ D.G p`. -/
noncomputable def tailShortComplex (p : ↥(Finset.Icc a b)) :
    ShortComplex (CochainComplex (finiteTwistingModule D) ℤ) :=
  ShortComplex.mk _ _ (X.tailMap_comp_tailGradedπ p)

lemma tailShortComplex_f (p : ↥(Finset.Icc a b)) :
    (X.tailShortComplex p).f = X.tailMap (Int.le_add_one le_rfl) :=
  rfl

lemma tailShortComplex_g (p : ↥(Finset.Icc a b)) :
    (X.tailShortComplex p).g = X.tailGradedπ p :=
  rfl

/-- The degreewise splitting of `tail (p + 1) ⟶ tail p ⟶ D.G p`. -/
noncomputable def tailShortComplexSplitting (p : ↥(Finset.Icc a b)) (n : ℤ) :
    ((X.tailShortComplex p).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := D.tailIncl p.val n ≫ D.tailProj (p.val + 1) n
  s := biproduct.ι (fun q : {q : ↥(Finset.Icc a b) // p.val ≤ q.val} ↦ (D.G q.val).X n)
    ⟨p, le_rfl⟩
  f_r := D.tailIncl_tailProj_tailIncl_tailProj (Int.le_add_one le_rfl) n
  s_g := biproduct.ι_π_self _ _
  id := D.tailSplitting_id p n

/-- The sequence `tail (p + 1) ⟶ tail p ⟶ D.G p` is short exact. -/
lemma tailShortComplex_shortExact (p : ↥(Finset.Icc a b)) :
    (X.tailShortComplex p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (X.tailShortComplexSplitting p n).shortExact

end FiniteTwistingMatrixData

end CochainComplex
