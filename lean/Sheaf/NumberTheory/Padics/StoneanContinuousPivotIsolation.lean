/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.ExtremallyDisconnected
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Sheaf.Topology.StoneanProjective
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Isolating one continuous pivot over a Stonean base

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 6.12(2),
printed p. 19; rectangular elimination variant
(blueprint: lem-sfb-stonean-continuous-pivot-isolation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Padic

private theorem stonean_section {P : Type v} [TopologicalSpace P] [CompactSpace P]
    [T2Space P] [ExtremallyDisconnected P] {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (q : X → P) (hq : Continuous q)
    (hqsurj : Function.Surjective q) :
    ∃ s : P → X, Continuous s ∧ ∀ p, q (s p) = p := by
  let P' := ULift.{u} P
  let X' := ULift.{v} X
  have : ExtremallyDisconnected P' :=
    extremallyDisconnected_of_homeo (Homeomorph.ulift.symm : P ≃ₜ P')
  have hproj : CompactT2.Projective P' :=
    (CompactT2.extremallyDisconnected_iff_projective_iff_section P').1.mp inferInstance
  let q' : X' → P' := fun x ↦ ⟨q x.down⟩
  have hq' : Continuous q' :=
    continuous_uliftUp.comp (hq.comp continuous_uliftDown)
  have hqsurj' : Function.Surjective q' := by
    intro p
    obtain ⟨x, hx⟩ := hqsurj p.down
    exact ⟨⟨x⟩, congrArg ULift.up hx⟩
  obtain ⟨s, hs, hsec⟩ := hproj continuous_id hq' hqsurj'
  refine ⟨fun p ↦ (s ⟨p⟩).down,
    continuous_uliftDown.comp (hs.comp continuous_uliftUp), ?_⟩
  intro p
  exact congrArg ULift.down (congrFun hsec (ULift.up p))

private theorem bounded_division
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (P : Type v) [TopologicalSpace P] [CompactSpace P] [T2Space P]
    [ExtremallyDisconnected P] (a b : P → E)
    (ha : @Continuous P E _
      (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace a)
    (hb : @Continuous P E _
      (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace b)
    (hab : ∀ p, @norm E (spectralNorm.normedField (Padic l) E).toNorm (a p) ≤
      @norm E (spectralNorm.normedField (Padic l) E).toNorm (b p)) :
    ∃ q : P → coefficientExtensionIntegers l E,
      (@Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (q p : E))) ∧ ∀ p, a p = b p * (q p : E) := by
  classical
  let : NormedField E := spectralNorm.normedField (Padic l) E
  let O := coefficientExtensionIntegers l E
  let : TopologicalSpace O := coefficientExtensionIntegersTopology l E
  have : CompactSpace O := (coefficientExtension_integers_profinite_tower.{u, 0} l E).2.1
  have : T2Space O := (coefficientExtension_integers_profinite_tower.{u, 0} l E).2.2.1
  have hcoe : Continuous (fun x : O ↦ (x : E)) := continuous_induced_dom
  have hmem : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1 :=
    (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec.1
  let Z : Set (P × O) := {z | a z.1 = b z.1 * (z.2 : E)}
  have hZ : IsClosed Z :=
    isClosed_eq (ha.comp continuous_fst)
      ((hb.comp continuous_fst).mul (hcoe.comp continuous_snd))
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let π : Z → P := fun z ↦ z.val.1
  have hπ : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπsurj : Function.Surjective π := by
    intro p
    by_cases hb0 : b p = 0
    · have ha0 : a p = 0 := by
        apply norm_eq_zero.mp
        exact le_antisymm (by simpa [hb0] using hab p) (norm_nonneg _)
      exact ⟨⟨(p, 0), by simp [Z, ha0, hb0]⟩, rfl⟩
    · have hquot : a p / b p ∈ O := by
        apply (hmem _).mpr
        rw [norm_div]
        exact (div_le_one (norm_pos_iff.mpr hb0)).mpr (hab p)
      refine ⟨⟨(p, ⟨a p / b p, hquot⟩), ?_⟩, rfl⟩
      change a p = b p * (a p / b p)
      field_simp
  obtain ⟨s, hs, hsec⟩ := stonean_section π hπ hπsurj
  refine ⟨fun p ↦ (s p).val.2,
    hcoe.comp (continuous_snd.comp (continuous_subtype_val.comp hs)), ?_⟩
  intro p
  have h := (s p).property
  change a (π (s p)) = b (π (s p)) * ((s p).val.2 : E) at h
  simpa only [hsec p] using h

private theorem continuous_max_label {P : Type v} [TopologicalSpace P] [CompactSpace P]
    [T2Space P] [ExtremallyDisconnected P] {ι : Type} [Finite ι] [Nonempty ι]
    (f : ι → P → ℝ) (hf : ∀ i, Continuous (f i)) :
    ∃ a : P → ι, @Continuous P ι _ ⊥ a ∧ ∀ p i, f i p ≤ f (a p) p := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  let Z : Set (P × ι) := {z | ∀ i, f i z.1 ≤ f z.2 z.1}
  have heval : Continuous (fun z : P × ι ↦ f z.2 z.1) :=
    continuous_prod_of_discrete_right.mpr hf
  have hZ : IsClosed Z := by
    change IsClosed {z : P × ι | ∀ i, f i z.1 ≤ f z.2 z.1}
    simp_rw [Set.ofPred_forall]
    exact isClosed_iInter (fun i ↦ isClosed_le ((hf i).comp continuous_fst) heval)
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let π : Z → P := fun z ↦ z.val.1
  have hπ : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπsurj : Function.Surjective π := by
    intro p
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ f i p)
      Finset.univ_nonempty
    exact ⟨⟨(p, i), fun j ↦ hi j (Finset.mem_univ _)⟩, rfl⟩
  obtain ⟨s, hs, hsec⟩ := stonean_section π hπ hπsurj
  refine ⟨fun p ↦ (s p).val.2,
    continuous_snd.comp (continuous_subtype_val.comp hs), ?_⟩
  intro p i
  have h := (s p).property i
  change f i (π (s p)) ≤ f (s p).val.2 (π (s p)) at h
  simpa only [hsec p] using h

private def permGL {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix.GeneralLinearGroup (Fin n) R where
  val := σ.permMatrix R
  inv := σ⁻¹.permMatrix R
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

private theorem permGL_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (σ : Equiv.Perm (Fin n)) :
    (permGL (R := R) σ).val.map f = (permGL (R := S) σ).val := by
  exact PEquiv.map_toMatrix f σ.toPEquiv

private def nilColumn {R : Type*} [Zero R] {n : ℕ} (q : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j ↦ Fin.cases 0 (fun i ↦ Fin.cases (q i) (fun _ ↦ 0) j) i

private theorem nilColumn_mul {R : Type*} [Semiring R] {n : ℕ} (q t : Fin n → R) :
    nilColumn q * nilColumn t = 0 := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    simp [nilColumn, Matrix.mul_apply, Fin.sum_univ_succ]

private def rowGL {R : Type*} [Ring R] {n : ℕ} (q : Fin n → R) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) R where
  val := 1 + nilColumn q
  inv := 1 - nilColumn q
  val_inv := by simp [mul_sub, add_mul, nilColumn_mul]
  inv_val := by simp [sub_mul, mul_add, nilColumn_mul]

private def colGL {R : Type*} [CommRing R] {n : ℕ} (q : Fin n → R) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) R where
  val := (rowGL q).val.transpose
  inv := (rowGL q).inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, (rowGL q).inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, (rowGL q).val_inv, Matrix.transpose_one]

private theorem rowGL_mul_zero {R : Type*} [Ring R] {n m : ℕ}
    (q : Fin n → R) (A : Matrix (Fin (n + 1)) (Fin m) R) (j : Fin m) :
    ((rowGL q).val * A) 0 j = A 0 j := by
  simp [rowGL, nilColumn, Matrix.mul_apply, Matrix.one_apply, eq_comm, add_comm]

private theorem rowGL_mul_succ {R : Type*} [Ring R] {n m : ℕ}
    (q : Fin n → R) (A : Matrix (Fin (n + 1)) (Fin m) R) (i : Fin n) (j : Fin m) :
    ((rowGL q).val * A) i.succ j = A i.succ j + q i * A 0 j := by
  simp [rowGL, nilColumn, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply, eq_comm, add_comm]

private theorem mul_colGL_zero {R : Type*} [CommRing R] {n m : ℕ}
    (q : Fin m → R) (A : Matrix (Fin n) (Fin (m + 1)) R) (i : Fin n) :
    (A * (colGL q).val) i 0 = A i 0 := by
  simp [colGL, rowGL, Matrix.transpose_add, nilColumn, Matrix.mul_apply,
    Matrix.one_apply, add_comm]

private theorem mul_colGL_succ {R : Type*} [CommRing R] {n m : ℕ}
    (q : Fin m → R) (A : Matrix (Fin n) (Fin (m + 1)) R) (i : Fin n) (j : Fin m) :
    (A * (colGL q).val) i j.succ = A i j.succ + A i 0 * q j := by
  simp [colGL, rowGL, Matrix.transpose_add, nilColumn, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.one_apply, eq_comm, add_comm]

private theorem rowGL_map {R S : Type*} [Ring R] [Ring S] {n : ℕ}
    (f : R →+* S) (q : Fin n → R) :
    (rowGL q).val.map f = (rowGL (fun i ↦ f (q i))).val := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp only [rowGL, nilColumn, Matrix.map_apply, Matrix.one_apply,
      Matrix.add_apply, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj,
      Fin.succ_ne_zero, map_add, map_zero]
  all_goals split_ifs <;> simp_all

private theorem colGL_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (q : Fin n → R) :
    (colGL q).val.map f = (colGL (fun i ↦ f (q i))).val := by
  exact congrArg Matrix.transpose (rowGL_map f q)

private theorem rowGL_continuous {R E : Type*} [Ring R] [Ring E]
    [TopologicalSpace E] [IsTopologicalRing E] {P : Type*} [TopologicalSpace P]
    {n : ℕ} (f : R →+* E) (q : P → Fin n → R)
    (hq : ∀ i, Continuous (fun p ↦ f (q p i))) :
    (∀ i j, Continuous (fun p ↦ f ((rowGL (q p)).val i j))) ∧
    (∀ i j, Continuous (fun p ↦ f (((rowGL (q p))⁻¹).val i j))) := by
  constructor
  · intro i j
    change Continuous (fun p ↦ f ((1 : Matrix _ _ R) i j + nilColumn (q p) i j))
    simp only [map_add]
    apply continuous_const.add
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      refine Fin.cases ?_ (fun j ↦ ?_) j
    · change Continuous (fun _ : P ↦ f 0)
      exact continuous_const
    · change Continuous (fun _ : P ↦ f 0)
      exact continuous_const
    · exact hq i
    · change Continuous (fun _ : P ↦ f 0)
      exact continuous_const
  · intro i j
    change Continuous (fun p ↦ f ((1 : Matrix _ _ R) i j - nilColumn (q p) i j))
    simp only [map_sub]
    apply continuous_const.sub
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      refine Fin.cases ?_ (fun j ↦ ?_) j
    · change Continuous (fun _ : P ↦ f 0)
      exact continuous_const
    · change Continuous (fun _ : P ↦ f 0)
      exact continuous_const
    · exact hq i
    · change Continuous (fun _ : P ↦ f 0)
      exact continuous_const

private theorem colGL_continuous {R E : Type*} [CommRing R] [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] {P : Type*} [TopologicalSpace P]
    {n : ℕ} (f : R →+* E) (q : P → Fin n → R)
    (hq : ∀ i, Continuous (fun p ↦ f (q p i))) :
    (∀ i j, Continuous (fun p ↦ f ((colGL (q p)).val i j))) ∧
    (∀ i j, Continuous (fun p ↦ f (((colGL (q p))⁻¹).val i j))) :=
  ⟨fun i j ↦ (rowGL_continuous f q hq).1 j i,
    fun i j ↦ (rowGL_continuous f q hq).2 j i⟩

private theorem continuous_entries_mul {R : Type*} [Semiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] {X : Type*} [TopologicalSpace X]
    {n m k : ℕ} {A : X → Matrix (Fin n) (Fin m) R}
    {B : X → Matrix (Fin m) (Fin k) R}
    (hA : ∀ i j, Continuous (fun x ↦ A x i j))
    (hB : ∀ i j, Continuous (fun x ↦ B x i j)) :
    ∀ i j, Continuous (fun x ↦ (A x * B x) i j) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact continuous_finsetSum _ (fun k _ ↦ (hA i k).mul (hB k j))

/-- Continuous integral row and column operations isolate the first pivot. Only the
remaining first row and first column vanish; the lower-right block is unrestricted.

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 6.12(2),
printed p. 19; steps 1--4 of the rectangular diagonalization argument
(blueprint: lem-sfb-stonean-continuous-pivot-isolation).

Proof: For continuous a,b with |a| ≤ |b|, the closed equation space
{(p,t) ∈ P × O_E : a(p) = b(p)t} is compact Hausdorff, since O_E is compact
by the integers profinite tower theorem. Its projection onto P is surjective:
use a(p)/b(p) when b(p) ≠ 0, and zero otherwise. Projectivity of the Stonean
base gives a continuous section, hence continuous integral bounded division a=bq.
For a finite nonempty family of continuous real functions f_i, the incidence
space {(p,i) : ∀ j, f_j(p)≤f_i(p)} is closed in P times the finite discrete index
set. It is compact Hausdorff, and projection is surjective since a finite family
has a maximum. A Stonean section supplies a continuous maximal index label.
Apply this to the norms of the matrix entries. Row and column permutation
matrices swapping the selected indices with zero have continuous entries and
inverses because they factor through the discrete index label. They move the
maximum to (0,0), giving A with |A_ij|≤|A_00|. Bounded division yields
A_i0=A_00 q_i and A_0j=A_00 t_j for positive indices. The matrices
R=I−∑ q_i e_i0 and C=I−∑ t_j e_0j have inverses with plus signs, since the
strict column and row sums square to zero. Direct multiplication shows RAC
has zero first row and column away from (0,0). Compose R and C with the
permutations. All entries and inverse entries are finite sums of products of
continuous integral functions. At zero pivots the division identities still hold;
on an empty base all identities are vacuous. No diagonalization of the remaining
block is asserted or used.
-/
theorem exists_continuous_integral_pivot_isolation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (P : Type v) [TopologicalSpace P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [ExtremallyDisconnected P]
    (n m : ℕ) (F : P → Matrix (Fin (n + 1)) (Fin (m + 1)) E)
    (hF : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)),
      @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ F p i j)) :
    ∃ (L : P → Matrix.GeneralLinearGroup (Fin (n + 1)) (coefficientExtensionIntegers l E))
      (U : P → Matrix.GeneralLinearGroup (Fin (m + 1)) (coefficientExtensionIntegers l E)),
      (∀ (i j : Fin (n + 1)), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ ((L p).val i j : E))) ∧
      (∀ (i j : Fin (n + 1)), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (((L p)⁻¹).val i j : E))) ∧
      (∀ (i j : Fin (m + 1)), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ ((U p).val i j : E))) ∧
      (∀ (i j : Fin (m + 1)), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (((U p)⁻¹).val i j : E))) ∧
      (∀ (p : P) (j : Fin m),
        ((L p).val.map (fun x ↦ (x : E)) * F p *
          (U p).val.map (fun x ↦ (x : E))) 0 j.succ = 0) ∧
      (∀ (p : P) (i : Fin n),
        ((L p).val.map (fun x ↦ (x : E)) * F p *
          (U p).val.map (fun x ↦ (x : E))) i.succ 0 = 0) := by
  classical
  let : NormedField E := spectralNorm.normedField (Padic l) E
  let O := coefficientExtensionIntegers l E
  let f : O →+* E := O.subtype
  obtain ⟨a, ha, hmax⟩ := continuous_max_label
    (fun ij : Fin (n + 1) × Fin (m + 1) ↦ fun p ↦ ‖F p ij.1 ij.2‖)
    (fun ij ↦ (hF ij.1 ij.2).norm)
  let : TopologicalSpace (Fin (n + 1) × Fin (m + 1)) := ⊥
  have : DiscreteTopology (Fin (n + 1) × Fin (m + 1)) := ⟨rfl⟩
  let S := fun p ↦ permGL (R := O) (Equiv.swap 0 (a p).1)
  let T := fun p ↦ permGL (R := O) (Equiv.swap 0 (a p).2)
  have hS : ∀ i j, Continuous (fun p ↦ f ((S p).val i j)) := by
    intro i j
    exact (continuous_of_discreteTopology (f := fun ij : Fin (n + 1) × Fin (m + 1) ↦
      f ((permGL (R := O) (Equiv.swap 0 ij.1)).val i j))).comp ha
  have hSi : ∀ i j, Continuous (fun p ↦ f (((S p)⁻¹).val i j)) := by
    intro i j
    exact (continuous_of_discreteTopology (f := fun ij : Fin (n + 1) × Fin (m + 1) ↦
      f (((permGL (R := O) (Equiv.swap 0 ij.1))⁻¹).val i j))).comp ha
  have hT : ∀ i j, Continuous (fun p ↦ f ((T p).val i j)) := by
    intro i j
    exact (continuous_of_discreteTopology (f := fun ij : Fin (n + 1) × Fin (m + 1) ↦
      f ((permGL (R := O) (Equiv.swap 0 ij.2)).val i j))).comp ha
  have hTi : ∀ i j, Continuous (fun p ↦ f (((T p)⁻¹).val i j)) := by
    intro i j
    exact (continuous_of_discreteTopology (f := fun ij : Fin (n + 1) × Fin (m + 1) ↦
      f (((permGL (R := O) (Equiv.swap 0 ij.2))⁻¹).val i j))).comp ha
  let A := fun p ↦ (S p).val.map f * F p * (T p).val.map f
  have hA : ∀ i j, Continuous (fun p ↦ A p i j) :=
    continuous_entries_mul (continuous_entries_mul hS hF) hT
  have hAeq (p : P) (i : Fin (n + 1)) (j : Fin (m + 1)) :
      A p i j = F p (Equiv.swap 0 (a p).1 i) (Equiv.swap 0 (a p).2 j) := by
    dsimp only [A, S, T]
    rw [permGL_map, permGL_map]
    simp [permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  have hbound (p : P) (i : Fin (n + 1)) (j : Fin (m + 1)) :
      ‖A p i j‖ ≤ ‖A p 0 0‖ := by
    simp only [hAeq, Equiv.swap_apply_left]
    exact hmax p (Equiv.swap 0 (a p).1 i, Equiv.swap 0 (a p).2 j)
  have hq (i : Fin n) := bounded_division l E P
    (fun p ↦ A p i.succ 0) (fun p ↦ A p 0 0)
    (hA i.succ 0) (hA 0 0) (fun p ↦ hbound p i.succ 0)
  choose q hqc hqe using hq
  have ht (j : Fin m) := bounded_division l E P
    (fun p ↦ A p 0 j.succ) (fun p ↦ A p 0 0)
    (hA 0 j.succ) (hA 0 0) (fun p ↦ hbound p 0 j.succ)
  choose t htc hte using ht
  let R := fun p ↦ rowGL (fun i ↦ -q i p)
  let C := fun p ↦ colGL (fun j ↦ -t j p)
  have hR := rowGL_continuous f (fun p i ↦ -q i p)
    (fun i ↦ by
      simp only [map_neg]
      change Continuous (fun p ↦ -(q i p : E))
      exact (hqc i).neg)
  have hC := colGL_continuous f (fun p j ↦ -t j p)
    (fun j ↦ by
      simp only [map_neg]
      change Continuous (fun p ↦ -(t j p : E))
      exact (htc j).neg)
  have hmap {k : ℕ} (V W : Matrix.GeneralLinearGroup (Fin k) O) :
      (V * W).val.map f = V.val.map f * W.val.map f := Matrix.map_mul
  refine ⟨fun p ↦ R p * S p, fun p ↦ T p * C p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ∀ i j, Continuous (fun p ↦ ((R p * S p).val.map f) i j)
    simp_rw [hmap]
    exact continuous_entries_mul hR.1 hS
  · change ∀ i j, Continuous (fun p ↦ (((R p * S p)⁻¹).val.map f) i j)
    simp_rw [mul_inv_rev, hmap]
    exact continuous_entries_mul hSi hR.2
  · change ∀ i j, Continuous (fun p ↦ ((T p * C p).val.map f) i j)
    simp_rw [hmap]
    exact continuous_entries_mul hT hC.1
  · change ∀ i j, Continuous (fun p ↦ (((T p * C p)⁻¹).val.map f) i j)
    simp_rw [mul_inv_rev, hmap]
    exact continuous_entries_mul hC.2 hTi
  · intro p j
    change ((R p * S p).val.map f * F p * (T p * C p).val.map f) 0 j.succ = 0
    rw [hmap, hmap]
    have heq : (R p).val.map f * (S p).val.map f * F p *
        ((T p).val.map f * (C p).val.map f) =
        (R p).val.map f * A p * (C p).val.map f := by
      simp only [A, Matrix.mul_assoc]
    rw [heq]
    change (((rowGL (fun i ↦ -q i p)).val.map f) * A p *
      (colGL (fun j ↦ -t j p)).val.map f) 0 j.succ = 0
    rw [rowGL_map, colGL_map, mul_colGL_succ, rowGL_mul_zero, rowGL_mul_zero]
    rw [hte j p, map_neg]
    change A p 0 0 * (t j p : E) + A p 0 0 * -(t j p : E) = 0
    ring
  · intro p i
    change ((R p * S p).val.map f * F p * (T p * C p).val.map f) i.succ 0 = 0
    rw [hmap, hmap]
    have heq : (R p).val.map f * (S p).val.map f * F p *
        ((T p).val.map f * (C p).val.map f) =
        (R p).val.map f * A p * (C p).val.map f := by
      simp only [A, Matrix.mul_assoc]
    rw [heq]
    change (((rowGL (fun i ↦ -q i p)).val.map f) * A p *
      (colGL (fun j ↦ -t j p)).val.map f) i.succ 0 = 0
    rw [rowGL_map, colGL_map, mul_colGL_zero, rowGL_mul_succ, hqe i p, map_neg]
    change A p 0 0 * (q i p : E) + -(q i p : E) * A p 0 0 = 0
    ring

end Padic
