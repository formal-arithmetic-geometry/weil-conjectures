/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidFiltration
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-!
# The column and row filtrations of the total complex of a first quadrant double complex

Let `K : HomologicalComplex₂ C (up ℕ) (up ℕ)` be a first quadrant double complex in an abelian
category `C`, with total complex `Tot K`. The *column filtration* `Fᵖ Tot K` is the total complex
of the double complex `K^{≥ p, •}` obtained by replacing the columns of index `< p` by zero
(the stupid truncation of `K`, seen as a complex of columns); it is a subcomplex of `Tot K`.
Its *image filtration* on cohomology is `Fᵖ Hⁿ(Tot K) = im (Hⁿ(Fᵖ Tot K) ⟶ Hⁿ(Tot K))`,
a decreasing filtration of `Hⁿ(Tot K)` with `F⁰ Hⁿ = Hⁿ` and `Fⁿ⁺¹ Hⁿ = 0`.

The *row filtration* is the column filtration of the transposed double complex `Kᵀ = K.flip`,
transported along the canonical isomorphism `Tot Kᵀ ≅ Tot K`
(`HomologicalComplex₂.totalFlipIso`, which needs the signs
`TotalComplexShapeSymmetry (up ℕ) (up ℕ) (up ℕ)` provided here).

These are the filtrations described in the blueprint node `sk-def-groth-ss`, whose two
spectral sequences abut to `H^•(Tot K)` with these image filtrations; that convergence statement
is `HomologicalComplex₂.exists_spectralSequence` and is not proved here.

## Main definitions

- `HomologicalComplex₂.columnTrunc`: the double complex `K^{≥ p, •}`.
- `HomologicalComplex₂.columnFiltrationι`: the inclusion `Fᵖ Tot K ⟶ Tot K`, a monomorphism.
- `HomologicalComplex₂.columnFiltration`: `Fᵖ Tot K` as a subobject of `Tot K`.
- `HomologicalComplex₂.homologyColumnFiltration`: the image filtration `Fᵖ Hⁿ(Tot K)`.
- `HomologicalComplex₂.rowFiltrationι`, `HomologicalComplex₂.rowFiltration`,
  `HomologicalComplex₂.homologyRowFiltration`: the same for the row filtration.
-/

@[expose] public section

open CategoryTheory Limits

namespace ComplexShape

set_option backward.isDefEq.respectTransparency.types false in
/-- The signs identifying the total complex of a double complex indexed by `up ℕ` with the total
complex of its transpose: `σ p q = (-1) ^ (p * q)`. -/
instance : TotalComplexShapeSymmetry (up ℕ) (up ℕ) (up ℕ) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, add_mul, one_mul, pow_add, ← mul_assoc, mul_right_comm, Int.units_mul_self,
      one_mul]
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, mul_add, mul_one, pow_add]

/-- The embedding `i ↦ i + p` of `up ℕ` into itself, whose image is the set of indices
`≥ p`. -/
def embeddingUpNatAdd (p : ℕ) : Embedding (up ℕ) (up ℕ) :=
  embeddingUp'Add 1 p

@[simp]
lemma embeddingUpNatAdd_f (p i : ℕ) : (embeddingUpNatAdd p).f i = i + p :=
  rfl

instance (p : ℕ) : (embeddingUpNatAdd p).IsRelIff :=
  inferInstanceAs (embeddingUp'Add 1 p).IsRelIff

instance (p : ℕ) : (embeddingUpNatAdd p).IsTruncGE :=
  inferInstanceAs (embeddingUp'Add 1 p).IsTruncGE

lemma embeddingUpNatAdd_subset {p p' : ℕ} (h : p ≤ p') :
    (embeddingUpNatAdd p').Subset (embeddingUpNatAdd p) where
  subset := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i + (p' - p), by simp; lia⟩

end ComplexShape

namespace HomologicalComplex₂

open ComplexShape

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex₂ C (up ℕ) (up ℕ))

/-- The double complex `K^{≥ p, •}`: the columns of index `< p` of `K` are replaced by zero.
It is the stupid truncation of `K`, seen as a complex of columns.

(blueprint: `sk-def-groth-ss`) -/
noncomputable abbrev columnTrunc (p : ℕ) : HomologicalComplex₂ C (up ℕ) (up ℕ) :=
  HomologicalComplex.stupidTrunc K (embeddingUpNatAdd p)

/-- The inclusion of double complexes `K^{≥ p, •} ⟶ K`. -/
noncomputable abbrev ιColumnTrunc (p : ℕ) : K.columnTrunc p ⟶ K :=
  HomologicalComplex.ιStupidTrunc K (embeddingUpNatAdd p)

/-- The inclusion `Fᵖ Tot K = Tot (K^{≥ p, •}) ⟶ Tot K` of the `p`-th step of the column
filtration of the total complex.

(blueprint: `sk-def-groth-ss`) -/
noncomputable def columnFiltrationι (p : ℕ) :
    (K.columnTrunc p).total (up ℕ) ⟶ K.total (up ℕ) :=
  total.map (K.ιColumnTrunc p) (up ℕ)

/-- A degreewise retraction of `columnFiltrationι`, induced by the projections of the columns of
`K` onto the columns of `K^{≥ p, •}`. It is not a morphism of complexes. -/
noncomputable def columnFiltrationRetractionX (p n : ℕ) :
    (K.total (up ℕ)).X n ⟶ ((K.columnTrunc p).total (up ℕ)).X n :=
  K.totalDesc fun i₁ i₂ h ↦
    (HomologicalComplex.πStupidTruncf K (embeddingUpNatAdd p) i₁).f i₂ ≫
    (K.columnTrunc p).ιTotal (up ℕ) i₁ i₂ n h

@[reassoc (attr := simp)]
lemma columnFiltrationι_f_retractionX (p n : ℕ) :
    (K.columnFiltrationι p).f n ≫ K.columnFiltrationRetractionX p n = 𝟙 _ := by
  refine total.hom_ext _ fun i₁ i₂ h ↦ ?_
  rw [columnFiltrationι, ιTotal_map_assoc, columnFiltrationRetractionX, ι_totalDesc,
    ← HomologicalComplex.comp_f_assoc, Category.comp_id]
  erw [HomologicalComplex.ιStupidTruncf_πStupidTruncf]
  rw [HomologicalComplex.id_f, Category.id_comp]

instance (p : ℕ) : Mono (K.columnFiltrationι p) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    (IsSplitMono.mk' ⟨_, K.columnFiltrationι_f_retractionX p n⟩).mono

/-- The `p`-th step `Fᵖ Tot K` of the column filtration of the total complex of a first quadrant
double complex, as a subcomplex of `Tot K`: the total complex of `K^{≥ p, •}`.

(blueprint: `sk-def-groth-ss`) -/
noncomputable def columnFiltration (p : ℕ) : Subobject (K.total (up ℕ)) :=
  Subobject.mk (K.columnFiltrationι p)

/-- The inclusions `Fᵖ' Tot K ⟶ Fᵖ Tot K ⟶ Tot K` for `p ≤ p'`. -/
@[reassoc]
lemma columnFiltrationι_fac {p p' : ℕ} (h : p ≤ p') :
    total.map (HomologicalComplex.mapStupidTruncGE K (embeddingUpNatAdd_subset h)) (up ℕ) ≫
      K.columnFiltrationι p = K.columnFiltrationι p' := by
  rw [columnFiltrationι, columnFiltrationι, ← total.map_comp,
    HomologicalComplex.mapStupidTruncGE_fac]

/-- The column filtration of the total complex is decreasing. -/
lemma columnFiltration_antitone {p p' : ℕ} (h : p ≤ p') :
    K.columnFiltration p' ≤ K.columnFiltration p :=
  Subobject.mk_le_mk_of_comm _ (K.columnFiltrationι_fac h)

instance : IsIso (K.ιColumnTrunc 0) := by
  have : K.IsStrictlySupported (embeddingUpNatAdd 0) := ⟨fun i' h ↦ (h i' rfl).elim⟩
  dsimp [ιColumnTrunc]
  infer_instance

instance : IsIso (K.columnFiltrationι 0) :=
  (total.mapIso (asIso (K.ιColumnTrunc 0)) (up ℕ)).isIso_hom

/-- The column filtration of the total complex is exhaustive: `F⁰ Tot K = Tot K`. -/
lemma columnFiltration_zero : K.columnFiltration 0 = ⊤ :=
  Subobject.mk_eq_top_of_isIso _

/-- In degree `n`, the step `Fⁿ⁺¹ Tot K` of the column filtration vanishes. -/
lemma isZero_columnTrunc_total_X (n : ℕ) :
    IsZero (((K.columnTrunc (n + 1)).total (up ℕ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  refine total.hom_ext _ fun i₁ i₂ h ↦ ?_
  refine IsZero.eq_of_src ?_ _ _
  refine (HomologicalComplex.eval _ _ i₂).map_isZero
    (HomologicalComplex.isZero_stupidTrunc_X _ _ _ fun i hi ↦ ?_)
  simp only [embeddingUpNatAdd_f] at hi
  have : i₁ + i₂ = n := h
  lia

/-- The image filtration `Fᵖ Hⁿ(Tot K) = im (Hⁿ(Fᵖ Tot K) ⟶ Hⁿ(Tot K))` on the
cohomology of the total complex of a first quadrant double complex, induced by the column
filtration.

(blueprint: `sk-def-groth-ss`) -/
noncomputable def homologyColumnFiltration (n p : ℕ) :
    Subobject ((K.total (up ℕ)).homology n) :=
  imageSubobject (HomologicalComplex.homologyMap (K.columnFiltrationι p) n)

/-- The image filtration induced by the column filtration is decreasing.

(blueprint: `sk-def-groth-ss`) -/
lemma homologyColumnFiltration_antitone (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    K.homologyColumnFiltration n p' ≤ K.homologyColumnFiltration n p := by
  simpa only [homologyColumnFiltration, ← HomologicalComplex.homologyMap_comp,
    K.columnFiltrationι_fac h] using imageSubobject_comp_le (HomologicalComplex.homologyMap
      (total.map (HomologicalComplex.mapStupidTruncGE K (embeddingUpNatAdd_subset h)) (up ℕ)) n)
      (HomologicalComplex.homologyMap (K.columnFiltrationι p) n)

/-- The image filtration induced by the column filtration is exhaustive: `F⁰ Hⁿ = Hⁿ`.

(blueprint: `sk-def-groth-ss`) -/
lemma homologyColumnFiltration_zero (n : ℕ) : K.homologyColumnFiltration n 0 = ⊤ := by
  rw [homologyColumnFiltration, imageSubobject_mono]
  exact Subobject.mk_eq_top_of_isIso _

/-- The image filtration induced by the column filtration is separated: `Fⁿ⁺¹ Hⁿ = 0`.

(blueprint: `sk-def-groth-ss`) -/
lemma homologyColumnFiltration_succ_self (n : ℕ) :
    K.homologyColumnFiltration n (n + 1) = ⊥ := by
  simp only [homologyColumnFiltration,
    (ShortComplex.isZero_homology_of_isZero_X₂ (((K.columnTrunc (n + 1)).total (up ℕ)).sc n)
      (K.isZero_columnTrunc_total_X n)).eq_of_src (HomologicalComplex.homologyMap _ n) 0]
  exact imageSubobject_zero

/-- The inclusion `Fᵖ Tot K ⟶ Tot K` of the `p`-th step of the row filtration of the total
complex: the column filtration of the transposed double complex `K.flip`, followed by the
isomorphism `Tot (K.flip) ≅ Tot K`.

(blueprint: `sk-def-groth-ss`) -/
noncomputable def rowFiltrationι (p : ℕ) :
    (K.flip.columnTrunc p).total (up ℕ) ⟶ K.total (up ℕ) :=
  K.flip.columnFiltrationι p ≫ (K.totalFlipIso (up ℕ)).hom

instance (p : ℕ) : Mono (K.rowFiltrationι p) := by
  dsimp [rowFiltrationι]
  infer_instance

/-- The `p`-th step of the row filtration of the total complex of a first quadrant double
complex, as a subcomplex of `Tot K`: the total complex of the rows of index `≥ p`.

(blueprint: `sk-def-groth-ss`) -/
noncomputable def rowFiltration (p : ℕ) : Subobject (K.total (up ℕ)) :=
  Subobject.mk (K.rowFiltrationι p)

/-- The inclusions `Fᵖ' ⟶ Fᵖ ⟶ Tot K` of the row filtration for `p ≤ p'`. -/
@[reassoc]
lemma rowFiltrationι_fac {p p' : ℕ} (h : p ≤ p') :
    total.map (HomologicalComplex.mapStupidTruncGE K.flip (embeddingUpNatAdd_subset h)) (up ℕ) ≫
      K.rowFiltrationι p = K.rowFiltrationι p' := by
  rw [rowFiltrationι, rowFiltrationι, K.flip.columnFiltrationι_fac_assoc h]

/-- The row filtration of the total complex is decreasing. -/
lemma rowFiltration_antitone {p p' : ℕ} (h : p ≤ p') :
    K.rowFiltration p' ≤ K.rowFiltration p :=
  Subobject.mk_le_mk_of_comm _ (K.rowFiltrationι_fac h)

instance : IsIso (K.rowFiltrationι 0) := by
  dsimp [rowFiltrationι]
  infer_instance

/-- The row filtration of the total complex is exhaustive. -/
lemma rowFiltration_zero : K.rowFiltration 0 = ⊤ :=
  Subobject.mk_eq_top_of_isIso _

/-- The image filtration `Fᵖ Hⁿ(Tot K) = im (Hⁿ(Fᵖ Tot K) ⟶ Hⁿ(Tot K))` on the
cohomology of the total complex of a first quadrant double complex, induced by the row filtration.

(blueprint: `sk-def-groth-ss`) -/
noncomputable def homologyRowFiltration (n p : ℕ) :
    Subobject ((K.total (up ℕ)).homology n) :=
  imageSubobject (HomologicalComplex.homologyMap (K.rowFiltrationι p) n)

/-- The image filtration induced by the row filtration is decreasing.

(blueprint: `sk-def-groth-ss`) -/
lemma homologyRowFiltration_antitone (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    K.homologyRowFiltration n p' ≤ K.homologyRowFiltration n p := by
  simpa only [homologyRowFiltration, ← HomologicalComplex.homologyMap_comp,
    K.rowFiltrationι_fac h] using imageSubobject_comp_le (HomologicalComplex.homologyMap
      (total.map (HomologicalComplex.mapStupidTruncGE K.flip (embeddingUpNatAdd_subset h))
        (up ℕ)) n)
      (HomologicalComplex.homologyMap (K.rowFiltrationι p) n)

/-- The image filtration induced by the row filtration is exhaustive: `F⁰ Hⁿ = Hⁿ`.

(blueprint: `sk-def-groth-ss`) -/
lemma homologyRowFiltration_zero (n : ℕ) : K.homologyRowFiltration n 0 = ⊤ := by
  rw [homologyRowFiltration, imageSubobject_mono]
  exact Subobject.mk_eq_top_of_isIso _

/-- The image filtration induced by the row filtration is separated: `Fⁿ⁺¹ Hⁿ = 0`.

(blueprint: `sk-def-groth-ss`) -/
lemma homologyRowFiltration_succ_self (n : ℕ) : K.homologyRowFiltration n (n + 1) = ⊥ := by
  simp only [homologyRowFiltration,
    (ShortComplex.isZero_homology_of_isZero_X₂
      (((K.flip.columnTrunc (n + 1)).total (up ℕ)).sc n)
      (K.flip.isZero_columnTrunc_total_X n)).eq_of_src (HomologicalComplex.homologyMap _ n) 0]
  exact imageSubobject_zero

end HomologicalComplex₂
