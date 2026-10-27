/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientDivisionData
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPowerSeries.Trunc

import Sheaf.RingTheory.InitialDiagramStabilization
import Sheaf.AlgebraicGeometry.CoefficientFirstExponentDeterminants
import Sheaf.AlgebraicGeometry.CoefficientRestrictedFiniteTests
import Sheaf.AlgebraicGeometry.CoefficientOrderLocusBound
import Sheaf.AlgebraicGeometry.CoefficientRestrictedToFull

/-! # Uniform coefficient orders and homogeneous division

Source: Bierstone--Milman, Invent. Math. 128 (1997), completion of Theorem 9.6,
p.282, using Theorem 8.1 and Lemma 7.7.
(blueprint: lem-trf-coefficient-locus-uniform-division)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonomialDiagram

namespace AlgebraicGeometry.HilbertCoefficient

private theorem coefficientFamilySeries_vertex {A L : Type u} [CommRing A] [Field L]
    {m n s : ℕ} (T : A →+* MvPowerSeries (Fin m) L)
    (c : Fin s → (Fin n →₀ ℕ) → A) (i : Fin s) (γ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (fullVertex m γ) (coefficientFamilySeries T c i) =
      MvPowerSeries.constantCoeff (T (c i γ)) := by
  have hl : Finsupp.comapDomain.addMonoidHom Sum.inl_injective (fullVertex m γ) = 0 := by
    ext j
    exact Finsupp.mapDomain_of_notMem_range γ (Sum.inl j) (by simp)
  have hr : Finsupp.comapDomain.addMonoidHom Sum.inr_injective (fullVertex m γ) = γ :=
    Finsupp.comapDomain_mapDomain _ Sum.inr_injective γ
  change MvPowerSeries.coeff _ (T (c i _)) = _
  rw [hl, hr]
  rfl

private theorem coefficient_restricted_coeff {A : Type u} [CommRing A] {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A) (q : ℕ)
    (i : {i : Fin s // (α i).degree ≤ q})
    (e : EssentialVariables (prefixVertices α q) →₀ ℕ) :
    MvPolynomial.coeff e (restrictedCoefficientForms α c q i) =
      if e.degree = (α i.val).degree then c i.val (Finsupp.mapDomain Subtype.val e) else 0 := by
  classical
  simp [restrictedCoefficientForms, MvPolynomial.coeff_sum, coefficientDegreeExponents,
    Finset.sum_ite_eq', and_iff_right_of_imp (fun h ↦ le_of_eq h)]

private theorem coefficient_matrix_entry {A : Type u} [CommRing A] {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A) (q t : ℕ)
    (row col : ↥(coefficientDegreeExponents
      (EssentialVariables (prefixVertices α q)) t)) :
    coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
        (restrictedCoefficientForms α c q) t row col = 0 ∨
    coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
        (restrictedCoefficientForms α c q) t row col = 1 ∨
    ∃ (i : Fin s) (γ : Fin n →₀ ℕ), γ.degree = (α i).degree ∧
      coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
        (restrictedCoefficientForms α c q) t row col = c i γ := by
  classical
  unfold coefficientDivisionMatrix
  split
  · rename_i h
    generalize Classical.choose h = p
    rcases p with p | e
    · simp only [divisionFamily, MvPolynomial.coeff_monomial_mul', one_mul]
      split
      · rw [coefficient_restricted_coeff]
        split
        · rename_i he
          exact Or.inr (Or.inr ⟨p.val.1.val,
            Finsupp.mapDomain Subtype.val (row.val - p.val.2),
            by rw [Finsupp.degree_mapDomain]; exact he, rfl⟩)
        · exact Or.inl rfl
      · exact Or.inl rfl
    · simp only [divisionFamily, MvPolynomial.coeff_monomial]
      split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · exact Or.inl rfl

private theorem coefficient_test_witness {A : Type u} [CommRing A] {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A)
    (B : ℕ → ℕ) (i : Fin s) : c i (α i) ∈ coefficientDivisionTests α c B := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

open Classical in
private theorem coefficient_test_det {A : Type u} [CommRing A] {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A)
    (B : ℕ → ℕ) (q t : ℕ)
    (hq : q ≤ Finset.univ.sup (fun i : Fin s ↦ (α i).degree)) (ht : t ≤ B q) :
    Matrix.det (coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
      (restrictedCoefficientForms α c q) t) ∈ coefficientDivisionTests α c B := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le hq),
      Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_of_le ht), rfl⟩⟩)

private theorem coefficient_tests_open {N : Scheme.{u}} {F : Finset Γ(N, ⊤)} (b : N) :
    b ∈ N.basicOpen (∏ g ∈ F, g) ↔ ∀ g ∈ F, N.Γevaluation b g ≠ 0 := by
  classical
  rw [← N.evaluation_ne_zero_iff_mem_basicOpen b (by trivial)]
  change (N.Γevaluation b).hom (∏ g ∈ F, g) ≠ 0 ↔ _
  simp only [map_prod, Finset.prod_ne_zero_iff]

private theorem coefficient_order_map {L : Type u} [Field L] {K : Type v} [Field K]
    {σ : Type} (j : L →+* K) (f : MvPowerSeries σ L) :
    (MvPowerSeries.map j f).order = f.order := by
  apply le_antisymm
  · apply MvPowerSeries.le_order
    intro e he
    apply j.injective
    simpa only [MvPowerSeries.coeff_map, map_zero] using
      (MvPowerSeries.coeff_of_lt_order he : MvPowerSeries.coeff e (MvPowerSeries.map j f) = 0)
  · exact MvPowerSeries.le_order_map j

open Classical in
/-- A single finite principal-open neighbourhood gives uniform orders and all prefix
homogeneous divisions, including after every extension of the residue field.

Source: BM 1997, completion of Theorem 9.6, p.282, using Theorem 8.1 and Lemma 7.7
(blueprint: lem-trf-coefficient-locus-uniform-division).

Proof:
1. Choose each essential-prefix bound from exists_finiteDivisionTest.
2. Constant Taylor coefficients are evaluations of the regular coefficients.
The first coefficients give the order witnesses, and
coefficient_first_exponent_determinants gives nonzero determinants at a.
Their finite product therefore defines a principal open containing a.
3. The coefficient formula for a monomial times a homogeneous finite sum gives
exactly the stated matrix-entry alternatives.
4. At b in the principal open all tests are nonzero. Apply
coefficient_restricted_finite_tests to obtain all restricted divisions, including
all field extensions. The proved coefficient_order_locus_bound and the nonzero
vertex coefficient give equality of orders.
5. Apply coefficient_restricted_to_full using the W-zero coefficient identities,
both over the residue field and over each extension. Injectivity of the field map
preserves orders and nonzero test values.
-/
theorem coefficient_locus_uniform_division {k : Type u} [Field k] [CharZero k]
    (N : Scheme.{u}) [IsAffine N] {m n s : ℕ}
    (w : MvPolynomial (Fin m) k →+* Γ(N, ⊤))
    (hsm : Smooth (N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (w.comp MvPolynomial.C))))
    (hft : LocallyOfFiniteType
      (N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (w.comp MvPolynomial.C))))
    (hqc : QuasiCompact
      (N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (w.comp MvPolynomial.C))))
    (hw : Etale (N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom w)))
    (T : ∀ b : N, Γ(N, ⊤) →+* MvPowerSeries (Fin m) (N.residueField b))
    (hT : ∀ b : N, isTaylorMap w (N.Γevaluation b).hom (T b))
    (c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)) (a : N)
    (D : Set (Fin n →₀ ℕ)) (α : Fin s → Fin n →₀ ℕ)
    (hD : IsMonotone D) (hα : IsOrderedVertexFamily D α)
    (hfirst : ∀ i : Fin s,
      MvPowerSeries.coeff (fullVertex m (α i)) (coefficientFamilySeries (T a) c i) ≠ 0 ∧
      ∀ e : (Fin m ⊕ Fin n) →₀ ℕ,
        Finsupp.DegLex (fun x y : Fin m ⊕ Fin n ↦ Sum.Lex (· < ·) (· < ·) x y) (· < ·)
          e (fullVertex m (α i)) →
        MvPowerSeries.coeff e (coefficientFamilySeries (T a) c i) = 0)
    (ha : a ∈ coefficientFamilyOrderLocus α c) :
    ∃ B : ℕ → ℕ,
      (∀ q : ℕ, ∀ (A : Type u) (_ : CommRing A),
        IsFiniteDivisionTest (generated (essentialVertices (prefixVertices α q)))
          (essentialVertices (prefixVertices α q)) A (B q)) ∧
      (∀ g ∈ coefficientDivisionTests α c B, N.Γevaluation a g ≠ 0) ∧
      a ∈ N.basicOpen (∏ g ∈ coefficientDivisionTests α c B, g) ∧
      (∀ (q t : ℕ), q ≤ Finset.univ.sup (fun i : Fin s ↦ (α i).degree) → t ≤ B q →
        ∀ row col,
          coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
            (restrictedCoefficientForms α c q) t row col = 0 ∨
          coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
            (restrictedCoefficientForms α c q) t row col = 1 ∨
          ∃ (i : Fin s) (γ : Fin n →₀ ℕ), γ.degree = (α i).degree ∧
            coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
              (restrictedCoefficientForms α c q) t row col = c i γ) ∧
      ∀ b : N, b ∈ coefficientFamilyOrderLocus α c →
        b ∈ N.basicOpen (∏ g ∈ coefficientDivisionTests α c B, g) →
        (∀ i : Fin s, (coefficientFamilySeries (T b) c i).order = ((α i).degree : ℕ∞)) ∧
        (∀ q t : ℕ, HasUniqueDivision
          (generated (essentialVertices (prefixVertices α q)))
          (essentialVertices (prefixVertices α q))
          (fun i ↦ MvPolynomial.map (N.Γevaluation b).hom (restrictedCoefficientForms α c q i))
          t) ∧
        (∀ q t : ℕ, HasUniqueDivision
          (generated (prefixVertices (fun i ↦ fullVertex m (α i)) q))
          (prefixVertices (fun i ↦ fullVertex m (α i)) q)
          (fun i ↦ MvPolynomial.homogeneousComponent (α i.val).degree
            (MvPowerSeries.truncTotal ((α i.val).degree + 1)
              (coefficientFamilySeries (T b) c i.val))) t) ∧
        ∀ (K : Type v) [Field K] (j : N.residueField b →+* K),
          (∀ i : Fin s,
            (MvPowerSeries.map j (coefficientFamilySeries (T b) c i)).order =
              ((α i).degree : ℕ∞)) ∧
          (∀ q t : ℕ, HasUniqueDivision
            (generated (prefixVertices (fun i ↦ fullVertex m (α i)) q))
            (prefixVertices (fun i ↦ fullVertex m (α i)) q)
            (fun i ↦ MvPolynomial.homogeneousComponent (α i.val).degree
              (MvPowerSeries.truncTotal ((α i.val).degree + 1)
                (MvPowerSeries.map j (coefficientFamilySeries (T b) c i.val)))) t) ∧
          (∀ g ∈ coefficientDivisionTests α c B, j (N.Γevaluation b g) ≠ 0) ∧
          ∀ q t : ℕ, HasUniqueDivision
            (generated (essentialVertices (prefixVertices α q)))
            (essentialVertices (prefixVertices α q))
            (fun i ↦ MvPolynomial.map (j.comp (N.Γevaluation b).hom)
              (restrictedCoefficientForms α c q i)) t := by
  classical
  have _ := hsm
  have _ := hft
  have _ := hqc
  have _ := hw
  have _ := ha
  obtain ⟨B, hB⟩ := Classical.skolem.mp
    (exists_finiteDivisionTest n s D α hD hα).2.2.2
  have hvertex : ∀ (b : N) (i : Fin s) (γ : Fin n →₀ ℕ),
      MvPowerSeries.coeff (fullVertex m γ) (coefficientFamilySeries (T b) c i) =
        N.Γevaluation b (c i γ) := by
    intro b i γ
    rw [coefficientFamilySeries_vertex]
    exact (hT b).1 _
  have hdet := coefficient_first_exponent_determinants α D hα c
    (N.Γevaluation a).hom (T a) (hT a).1 hfirst
  have htests : ∀ g ∈ coefficientDivisionTests α c B, N.Γevaluation a g ≠ 0 := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      rw [← hvertex a i (α i)]
      exact (hfirst i).1
    · obtain ⟨q, _, hg⟩ := Finset.mem_biUnion.mp hg
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hg
      exact hdet q t
  refine ⟨B, hB, htests, (coefficient_tests_open a).mpr htests, ?_, ?_⟩
  · intro q t _ _ row col
    exact coefficient_matrix_entry α c q t row col
  · intro b hb hopen
    have hnonzero := (coefficient_tests_open b).mp hopen
    have hrestricted := coefficient_restricted_finite_tests α D hα c B hB
      (N.Γevaluation b).hom (fun q t hq ht ↦
        hnonzero _ (coefficient_test_det α c B q t hq ht))
    have horders : ∀ i : Fin s,
        (coefficientFamilySeries (T b) c i).order = ((α i).degree : ℕ∞) := by
      intro i
      apply le_antisymm
      · have hc : MvPowerSeries.coeff (fullVertex m (α i))
            (coefficientFamilySeries (T b) c i) ≠ 0 := by
          rw [hvertex]
          exact hnonzero _ (coefficient_test_witness α c B i)
        simpa [fullVertex] using MvPowerSeries.order_le hc
      · exact coefficient_order_locus_bound α c b (T b) (hT b).1 hb i
    refine ⟨horders, hrestricted.1, ?_, ?_⟩
    · exact coefficient_restricted_to_full α D hα c (N.Γevaluation b).hom
        (fun i ↦ coefficientFamilySeries (T b) c i) (hvertex b) hrestricted.1
    · intro K _ j
      refine ⟨?_, ?_, ?_, hrestricted.2 K j⟩
      · intro i
        rw [coefficient_order_map, horders]
      · apply coefficient_restricted_to_full α D hα c (j.comp (N.Γevaluation b).hom)
          (fun i ↦ MvPowerSeries.map j (coefficientFamilySeries (T b) c i))
        · intro i γ
          simp only [MvPowerSeries.coeff_map, hvertex, RingHom.comp_apply]
        · exact hrestricted.2 K j
      · intro g hg
        exact (map_ne_zero j).mpr (hnonzero g hg)

end AlgebraicGeometry.HilbertCoefficient
