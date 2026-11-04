/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationMatrix
public import WeilConjectures.Mathlib.Algebra.Homology.Additive

/-! # Tails of a finite twisting totalization

Given matrix data `X` for a finite twisting family `D`, the summands of weight at least `r`
form a subcomplex of `X.P`, because every matrix entry of the differential raises weight.
We construct these tails as complexes, their inclusions into `X.P`, the resulting decreasing
filtration of `X.P`, and identify its graded pieces with the complexes `D.G p`.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

/-- The direct sum of the degree-`n` terms of the complexes of weight at least `r`. -/
noncomputable abbrev FiniteTwistingFamily.tailSum (D : FiniteTwistingFamily R a b) (r n : ℤ) :
    finiteTwistingModule D :=
  ⨁ fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n

namespace FiniteTwistingMatrixData

variable {D : FiniteTwistingFamily R a b} (X : FiniteTwistingMatrixData D)

/-- The inclusion of the summands of weight at least `r` in degree `n`. -/
noncomputable def tailι (r n : ℤ) : D.tailSum r n ⟶ X.P.X n :=
  biproduct.desc fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val ≫ (X.coordinates n).inv

/-- The projection onto the summands of weight at least `r` in degree `n`. -/
noncomputable def tailRetraction (r n : ℤ) : X.P.X n ⟶ D.tailSum r n :=
  (X.coordinates n).hom ≫ biproduct.lift fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦
    biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val

@[reassoc]
lemma ι_tailι (r n : ℤ) (p : {p : ↥(Finset.Icc a b) // r ≤ p.val}) :
    biproduct.ι (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n) p ≫
        X.tailι r n =
      biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val ≫ (X.coordinates n).inv :=
  biproduct.ι_desc _ _

@[reassoc]
lemma tailRetraction_π (r n : ℤ) (p : {p : ↥(Finset.Icc a b) // r ≤ p.val}) :
    X.tailRetraction r n ≫
        biproduct.π (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n) p =
      (X.coordinates n).hom ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val := by
  rw [tailRetraction, Category.assoc, biproduct.lift_π]

/-- A summand of weight at least `r` is sent by the tail projection to the same summand. -/
@[reassoc]
lemma ι_coordinates_inv_tailRetraction (r n : ℤ) (q : ↥(Finset.Icc a b)) (h : r ≤ q.val) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q ≫ (X.coordinates n).inv ≫
        X.tailRetraction r n =
      biproduct.ι (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n)
        ⟨q, h⟩ := by
  refine biproduct.hom_ext _ _ fun p ↦ ?_
  rw [Category.assoc, Category.assoc, tailRetraction_π, Iso.inv_hom_id_assoc]
  obtain ⟨p, hp⟩ := p
  by_cases hqp : q = p
  · subst hqp
    rw [biproduct.ι_π_self, biproduct.ι_π_self]
  · rw [biproduct.ι_π_ne _ hqp, biproduct.ι_π_ne _ fun e ↦ hqp (congrArg Subtype.val e)]

/-- A summand of weight less than `r` is killed by the tail projection. -/
@[reassoc]
lemma ι_coordinates_inv_tailRetraction_of_lt (r n : ℤ) (q : ↥(Finset.Icc a b))
    (h : q.val < r) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) q ≫ (X.coordinates n).inv ≫
        X.tailRetraction r n = 0 := by
  refine biproduct.hom_ext _ _ fun p ↦ ?_
  rw [Category.assoc, Category.assoc, tailRetraction_π, Iso.inv_hom_id_assoc, zero_comp,
    biproduct.ι_π_ne _ fun e ↦ (lt_of_lt_of_le h p.2).ne (congrArg Subtype.val e)]

@[reassoc (attr := simp)]
lemma tailι_tailRetraction (r n : ℤ) : X.tailι r n ≫ X.tailRetraction r n = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun p ↦ ?_
  rw [ι_tailι_assoc, ι_coordinates_inv_tailRetraction _ _ _ _ p.2, Category.comp_id]

/-- The tail of weight at least `r'` lies in the tail of weight at least `r` when `r ≤ r'`. -/
@[reassoc]
lemma tailι_tailRetraction_tailι_of_le {r r' : ℤ} (h : r ≤ r') (n : ℤ) :
    X.tailι r' n ≫ X.tailRetraction r n ≫ X.tailι r n = X.tailι r' n := by
  refine biproduct.hom_ext' _ _ fun p ↦ ?_
  rw [ι_tailι_assoc, ι_coordinates_inv_tailRetraction_assoc _ _ _ _ (h.trans p.2), ι_tailι,
    ι_tailι]

/-- Below the weight interval the tail projection is inverse to the tail inclusion. -/
lemma tailRetraction_tailι_of_le {r : ℤ} (h : r ≤ a) (n : ℤ) :
    X.tailRetraction r n ≫ X.tailι r n = 𝟙 _ := by
  rw [← cancel_epi (X.coordinates n).inv]
  refine biproduct.hom_ext' _ _ fun q ↦ ?_
  rw [ι_coordinates_inv_tailRetraction_assoc _ _ _ _ (h.trans (Finset.mem_Icc.1 q.2).1),
    ι_tailι, Category.comp_id]

/-- The tail inclusions are compatible with the differential, since every matrix entry
raises weight. -/
lemma tailι_d_tailRetraction_tailι (r n m : ℤ) :
    X.tailι r n ≫ X.P.d n m ≫ X.tailRetraction r m ≫ X.tailι r m =
      X.tailι r n ≫ X.P.d n m := by
  by_cases hnm : n + 1 = m
  · subst hnm
    refine biproduct.hom_ext' _ _ fun p ↦ ?_
    rw [ι_tailι_assoc, ι_tailι_assoc, reassoc_of% (X.differential p.val n),
      X.differential p.val n, Preadditive.add_comp, Preadditive.sum_comp]
    congr 1
    · rw [Category.assoc, Category.assoc, ι_coordinates_inv_tailRetraction_assoc _ _ _ _ p.2,
        ι_tailι]
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Category.assoc, Category.assoc,
        ι_coordinates_inv_tailRetraction_assoc _ _ _ _ (p.2.trans q.2.le), ι_tailι]
  · rw [X.P.shape n m hnm, zero_comp, comp_zero]

/-- The diagonal entry of the differential matrix. -/
lemma ι_coordinates_inv_d_coordinates_hom_π_self (p : ↥(Finset.Icc a b)) (n : ℤ) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫ (X.coordinates n).inv ≫
        X.P.d n (n + 1) ≫ (X.coordinates (n + 1)).hom ≫
          biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) p =
      (D.G p).d n (n + 1) := by
  rw [reassoc_of% (X.differential p n), Preadditive.add_comp, Preadditive.sum_comp,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self, Category.comp_id,
    Finset.sum_eq_zero, add_zero]
  intro q _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    biproduct.ι_π_ne _ fun e ↦ lt_irrefl _ (lt_of_lt_of_eq q.2 (congrArg Subtype.val e)),
    comp_zero]

/-- The entries of the differential matrix below the diagonal vanish. -/
lemma ι_coordinates_inv_d_coordinates_hom_π_of_lt (p t : ↥(Finset.Icc a b))
    (h : p.val < t.val) (n : ℤ) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) t ≫ (X.coordinates n).inv ≫
        X.P.d n (n + 1) ≫ (X.coordinates (n + 1)).hom ≫
          biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) p = 0 := by
  rw [reassoc_of% (X.differential t n), Preadditive.add_comp, Preadditive.sum_comp,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    biproduct.ι_π_ne _ fun e ↦ h.ne' (congrArg Subtype.val e), comp_zero, zero_add]
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    biproduct.ι_π_ne _ fun e ↦ (h.trans q.2).ne' (congrArg Subtype.val e), comp_zero]

/-- The tail complex of the summands of weight at least `r`. -/
noncomputable def tail (r : ℤ) : CochainComplex (finiteTwistingModule D) ℤ :=
  HomologicalComplex.ofRetract X.P (D.tailSum r) (X.tailι r) (X.tailRetraction r)
    (X.tailι_d_tailRetraction_tailι r)

lemma tail_d (r n m : ℤ) :
    (X.tail r).d n m = X.tailι r n ≫ X.P.d n m ≫ X.tailRetraction r m := rfl

/-- The inclusion of the tail complex of weight at least `r`. -/
noncomputable def tailHom (r : ℤ) : X.tail r ⟶ X.P :=
  HomologicalComplex.ofRetractι X.P (D.tailSum r) (X.tailι r) (X.tailRetraction r)
    (X.tailι_d_tailRetraction_tailι r)

instance (r : ℤ) : Mono (X.tailHom r) :=
  HomologicalComplex.mono_ofRetractι _ _ _ _ _ (X.tailι_tailRetraction r)

/-- The inclusion of the tail of weight at least `r'` in the tail of weight at least `r`. -/
noncomputable def tailMap {r r' : ℤ} (h : r ≤ r') : X.tail r' ⟶ X.tail r :=
  HomologicalComplex.ofRetractMap X.P (X.tailι_tailRetraction_tailι_of_le h)

lemma tailMap_f {r r' : ℤ} (h : r ≤ r') (n : ℤ) :
    (X.tailMap h).f n = X.tailι r' n ≫ X.tailRetraction r n := rfl

@[reassoc (attr := simp)]
lemma tailMap_comp_tailHom {r r' : ℤ} (h : r ≤ r') :
    X.tailMap h ≫ X.tailHom r = X.tailHom r' :=
  HomologicalComplex.ofRetractMap_comp_ofRetractι X.P _

/-- The decreasing filtration of `X.P` by the tails. -/
noncomputable def tailFiltration : DecreasingFiltration X.P where
  F r := Subobject.mk (X.tailHom r)
  F_succ_le _ := Subobject.mk_le_mk_of_comm (X.tailMap (Int.le_add_one le_rfl))
    (X.tailMap_comp_tailHom _)

/-- The coordinates of the degree-`n` term of the tail filtration step `r`. -/
noncomputable def tailFiltrationCoordinates (r n : ℤ) :
    ((X.tailFiltration.step r : CochainComplex _ ℤ).X n) ≅ D.tailSum r n :=
  (HomologicalComplex.eval _ _ n).mapIso (Subobject.underlyingIso (X.tailHom r))

lemma tailFiltrationCoordinates_inv_arrow (r n : ℤ) :
    (X.tailFiltrationCoordinates r n).inv ≫ (X.tailFiltration.step r).arrow.f n =
      X.tailι r n :=
  congrArg (fun φ ↦ φ.f n) (Subobject.underlyingIso_arrow (X.tailHom r))

lemma tailFiltration_arrow_f (r n : ℤ) :
    (X.tailFiltration.step r).arrow.f n = (X.tailFiltrationCoordinates r n).hom ≫ X.tailι r n :=
  congrArg (fun φ ↦ φ.f n) (Subobject.underlyingIso_hom_comp_eq_mk (X.tailHom r)).symm

/-- The tail filtration step `r` is everything when `r ≤ a`. -/
lemma tailFiltration_step_eq_top {r : ℤ} (h : r ≤ a) : X.tailFiltration.step r = ⊤ := by
  have (n : ℤ) : IsIso ((X.tailHom r).f n) :=
    ⟨⟨X.tailRetraction r n, X.tailι_tailRetraction r n, X.tailRetraction_tailι_of_le h n⟩⟩
  have := HomologicalComplex.Hom.isIso_of_components (X.tailHom r)
  exact Subobject.mk_eq_top_of_isIso _

/-- The tail filtration step `r` is zero when `b < r`. -/
lemma tailFiltration_step_eq_bot {r : ℤ} (h : b < r) : X.tailFiltration.step r = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.2 (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)
  refine biproduct.hom_ext' _ _ fun p ↦ absurd p.2 ?_
  have := (Finset.mem_Icc.1 p.1.2).2
  omega

/-- The projection of the tail of weight at least `p` onto the summand of weight `p`. -/
noncomputable def tailGradedProjection (p : ↥(Finset.Icc a b)) : X.tail p.val ⟶ D.G p where
  f n := biproduct.π (fun t : {t : ↥(Finset.Icc a b) // p.val ≤ t.val} ↦ (D.G t.val).X n)
    ⟨p, le_rfl⟩
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    refine biproduct.hom_ext' _ _ fun t ↦ ?_
    rw [tail_d, Category.assoc, Category.assoc, tailRetraction_π, ι_tailι_assoc]
    obtain ⟨t, ht⟩ := t
    rcases ht.eq_or_lt with h | h
    · obtain rfl : t = p := Subtype.ext h.symm
      rw [biproduct.ι_π_self_assoc, ι_coordinates_inv_d_coordinates_hom_π_self]
    · rw [biproduct.ι_π_ne_assoc _ fun e ↦ h.ne' (congrArg (fun x ↦ x.val.val) e), zero_comp,
        ι_coordinates_inv_d_coordinates_hom_π_of_lt _ _ _ h]

lemma tailGradedProjection_f (p : ↥(Finset.Icc a b)) (n : ℤ) :
    (X.tailGradedProjection p).f n =
      biproduct.π (fun t : {t : ↥(Finset.Icc a b) // p.val ≤ t.val} ↦ (D.G t.val).X n)
        ⟨p, le_rfl⟩ := rfl

/-- The composite of the tail inclusion with a coordinate projection is the corresponding
projection of the tail. -/
lemma tailι_coordinates_hom_π (r n : ℤ) (p : {p : ↥(Finset.Icc a b) // r ≤ p.val}) :
    X.tailι r n ≫ (X.coordinates n).hom ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val =
      biproduct.π (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n) p := by
  rw [← tailRetraction_π, tailι_tailRetraction_assoc]

/-- The next tail is killed by the projection onto the summand of weight `p`. -/
@[reassoc]
lemma tailι_tailRetraction_π_self (p : ↥(Finset.Icc a b)) (n : ℤ) :
    X.tailι (p.val + 1) n ≫ X.tailRetraction p.val n ≫
        biproduct.π (fun t : {t : ↥(Finset.Icc a b) // p.val ≤ t.val} ↦ (D.G t.val).X n)
          ⟨p, le_rfl⟩ = 0 := by
  rw [tailRetraction_π]
  refine biproduct.hom_ext' _ _ fun t ↦ ?_
  rw [ι_tailι_assoc, Iso.inv_hom_id_assoc, comp_zero,
    biproduct.ι_π_ne _ fun e ↦ by
      have h : t.val.val = p.val := congrArg Subtype.val e
      have := t.2
      omega]

/-- The next tail is killed by the graded projection. -/
@[reassoc (attr := simp)]
lemma tailMap_comp_tailGradedProjection (p : ↥(Finset.Icc a b)) :
    X.tailMap (Int.le_add_one le_rfl : p.val ≤ p.val + 1) ≫ X.tailGradedProjection p = 0 :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    (Category.assoc _ _ _).trans (X.tailι_tailRetraction_π_self p n)

/-- The comparison of tails is the inclusion of the corresponding subobjects. -/
lemma underlyingIso_hom_tailMap {r r' : ℤ} (h : r ≤ r') :
    (Subobject.underlyingIso (X.tailHom r')).hom ≫ X.tailMap h =
      Subobject.ofLE (Subobject.mk (X.tailHom r')) (Subobject.mk (X.tailHom r))
          (Subobject.mk_le_mk_of_comm (X.tailMap h) (X.tailMap_comp_tailHom h)) ≫
        (Subobject.underlyingIso (X.tailHom r)).hom := by
  rw [Subobject.ofLE_mk_le_mk_of_comm _ (X.tailMap_comp_tailHom h), Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The short complex `tail (p + 1) ⟶ tail p ⟶ D.G p`. -/
noncomputable def tailShortComplex (p : ↥(Finset.Icc a b)) :
    ShortComplex (CochainComplex (finiteTwistingModule D) ℤ) :=
  ShortComplex.mk _ _ (X.tailMap_comp_tailGradedProjection p)

lemma tailShortComplex_split_f_r (p : ↥(Finset.Icc a b)) (n : ℤ) :
    (X.tailι (p.val + 1) n ≫ X.tailRetraction p.val n) ≫
        (X.tailι p.val n ≫ X.tailRetraction (p.val + 1) n) = 𝟙 _ := by
  rw [Category.assoc, X.tailι_tailRetraction_tailι_of_le_assoc (Int.le_add_one le_rfl),
    tailι_tailRetraction]

lemma tailShortComplex_split_id (p : ↥(Finset.Icc a b)) (n : ℤ) :
    (X.tailι p.val n ≫ X.tailRetraction (p.val + 1) n) ≫
        (X.tailι (p.val + 1) n ≫ X.tailRetraction p.val n) +
      biproduct.π (fun t : {t : ↥(Finset.Icc a b) // p.val ≤ t.val} ↦ (D.G t.val).X n)
          ⟨p, le_rfl⟩ ≫
        biproduct.ι (fun t : {t : ↥(Finset.Icc a b) // p.val ≤ t.val} ↦ (D.G t.val).X n)
          ⟨p, le_rfl⟩ = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun t ↦ ?_
  rw [Preadditive.comp_add, Category.comp_id, Category.assoc, ι_tailι_assoc]
  obtain ⟨t, ht⟩ := t
  rcases ht.eq_or_lt with h | h
  · obtain rfl : t = p := Subtype.ext h.symm
    rw [ι_coordinates_inv_tailRetraction_of_lt_assoc _ _ _ _ (lt_add_one _), zero_comp, zero_add,
      biproduct.ι_π_self_assoc]
  · rw [ι_coordinates_inv_tailRetraction_assoc _ _ _ _ (Int.add_one_le_iff.2 h), ι_tailι_assoc,
      ι_coordinates_inv_tailRetraction _ _ _ _ ht,
      biproduct.ι_π_ne_assoc _ fun e ↦ h.ne' (congrArg (fun x ↦ x.val.val) e), zero_comp,
      add_zero]

/-- The tail short complex is degreewise split. -/
noncomputable def tailShortComplexSplitting (p : ↥(Finset.Icc a b)) (n : ℤ) :
    ((X.tailShortComplex p).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := X.tailι p.val n ≫ X.tailRetraction (p.val + 1) n
  s := biproduct.ι (fun t : {t : ↥(Finset.Icc a b) // p.val ≤ t.val} ↦ (D.G t.val).X n)
    ⟨p, le_rfl⟩
  f_r := X.tailShortComplex_split_f_r p n
  s_g := biproduct.ι_π_self _ _
  id := X.tailShortComplex_split_id p n

lemma tailShortComplex_shortExact (p : ↥(Finset.Icc a b)) :
    (X.tailShortComplex p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (X.tailShortComplexSplitting p n).shortExact

/-- The short complex `F^{p+1} ⟶ F^p ⟶ D.G p` of the tail filtration. -/
noncomputable def tailFiltrationShortComplex (p : ↥(Finset.Icc a b)) :
    ShortComplex (CochainComplex (finiteTwistingModule D) ℤ) :=
  ShortComplex.mk
    (Subobject.ofLE (Subobject.mk (X.tailHom (p.val + 1))) (Subobject.mk (X.tailHom p.val))
      (Subobject.mk_le_mk_of_comm (X.tailMap (Int.le_add_one le_rfl))
        (X.tailMap_comp_tailHom (Int.le_add_one le_rfl))))
    ((Subobject.underlyingIso (X.tailHom p.val)).hom ≫ X.tailGradedProjection p) (by
      rw [Subobject.ofLE_mk_le_mk_of_comm _ (X.tailMap_comp_tailHom (Int.le_add_one le_rfl)),
        Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, tailMap_comp_tailGradedProjection,
        comp_zero])

/-- The filtration short complex is isomorphic to the tail short complex. -/
noncomputable def tailFiltrationShortComplexIso (p : ↥(Finset.Icc a b)) :
    X.tailFiltrationShortComplex p ≅ X.tailShortComplex p :=
  ShortComplex.isoMk (Subobject.underlyingIso (X.tailHom (p.val + 1)))
    (Subobject.underlyingIso (X.tailHom p.val)) (Iso.refl _)
    (X.underlyingIso_hom_tailMap (Int.le_add_one le_rfl)) (Category.comp_id _).symm

/-- The graded projection exhibits `D.G p` as the cokernel of `F^{p+1} ⟶ F^p`. -/
noncomputable def tailFiltrationIsColimit (p : ↥(Finset.Icc a b)) :
    IsColimit (CokernelCofork.ofπ _ (X.tailFiltrationShortComplex p).zero) :=
  (ShortComplex.shortExact_of_iso (X.tailFiltrationShortComplexIso p).symm
    (X.tailShortComplex_shortExact p)).gIsCokernel

/-- The graded pieces of the tail filtration are the complexes `D.G p`. -/
noncomputable def tailFiltrationGradedIso (p : ↥(Finset.Icc a b)) :
    X.tailFiltration.gradedPiece p.val ≅ D.G p :=
  (colimit.isColimit _).coconePointUniqueUpToIso (X.tailFiltrationIsColimit p)

lemma complexQuotientπ_tailFiltrationGradedIso_hom (p : ↥(Finset.Icc a b)) :
    X.tailFiltration.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl) ≫
        (X.tailFiltrationGradedIso p).hom =
      (Subobject.underlyingIso (X.tailHom p.val)).hom ≫ X.tailGradedProjection p :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (X.tailFiltrationIsColimit p) WalkingParallelPair.one

/-- Outside the weight interval the graded pieces of the tail filtration vanish. -/
lemma isZero_tailFiltration_gradedPiece (p : ℤ) (hp : p < a ∨ b < p) :
    IsZero (X.tailFiltration.gradedPiece p) := by
  have hle : X.tailFiltration.F p ≤ X.tailFiltration.F (p + 1) := by
    rcases hp with hp | hp
    · exact le_top.trans_eq (X.tailFiltration_step_eq_top (by omega : p + 1 ≤ a)).symm
    · exact (X.tailFiltration_step_eq_bot hp).trans_le bot_le
  have : Epi (Subobject.ofLE _ _ (X.tailFiltration.F_succ_le p)) :=
    (SplitEpi.mk (Subobject.ofLE _ _ hle) (by rw [Subobject.ofLE_comp_ofLE,
      Subobject.ofLE_refl])).epi
  exact isZero_cokernel_of_epi _

end FiniteTwistingMatrixData

end CochainComplex
