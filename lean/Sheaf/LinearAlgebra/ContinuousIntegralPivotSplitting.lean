/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q21, S8
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Topology.Sets.Opens
import Sheaf.NumberTheory.Padics.ContinuousUniformizerDivision
import Sheaf.LinearAlgebra.Matrix.ContinuousUnitPivot
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Local splitting of a continuous integral dominating pivot

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, proof of Theorem 6.12(2),
finite extension case, pp. 18–19. This is the agent auxiliary pivot lemma extracted
from the continuous integral Smith argument, not a theorem stated verbatim in HRS
(blueprint: lem-sfb-continuous-integral-pivot-splitting).

The positive matrix dimensions are written `1 + n` and `1 + m`, using the index
sets `Fin 1 ⊕ Fin n` and `Fin 1 ⊕ Fin m` so that the first coordinate is explicit.
-/

@[expose] public section

universe u v

namespace Padic

private theorem pivotTopology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    coefficientExtensionIntegersTopology l E =
      TopologicalSpace.induced (fun x : coefficientExtensionIntegers l E ↦ (x : E))
        (@UniformSpace.toTopologicalSpace E
          (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace) := by
  unfold coefficientExtensionIntegersTopology
  congr 1
  have h : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) =
        coefficientExtensionAbsoluteValue l E (-x + y)
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  exact congrArg (fun m ↦ m.toUniformSpace.toTopologicalSpace) h

private def pivotIndex (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun := Fin.cases (Sum.inl 0) Sum.inr
  invFun := Sum.elim (fun _ ↦ 0) Fin.succ
  left_inv i := by
    exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv i := by
    rcases i with i | i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rfl

/-- The continuous quotient and local unit property for an arbitrary generator of the
maximal ideal. This is the division step used by the pivot splitting theorem.

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, proof of Theorem 6.12(2),
finite extension case, pp. 18--19 (blueprint: lem-sfb-continuous-integral-pivot-splitting).
Proof: the maximal ideal is nonzero, so its generator is nonzero. Define the quotient
entrywise by division in the ambient field. Divisibility proves integrality, field
division proves continuity, and cancellation identifies the pivot quotient with the given unit. -/
private theorem continuous_integral_pivot_division
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (T : Type v) [TopologicalSpace T] (m n : ℕ)
    (G : T → Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E))
    (hG : ∀ (i : Fin 1 ⊕ Fin n) (j : Fin 1 ⊕ Fin m),
      @Continuous T (coefficientExtensionIntegers l E) _
        (coefficientExtensionIntegersTopology l E)
        (fun t ↦ G t i j))
    (e : ℕ) (t₀ : T)
    (hdiv : ∀ (t : T) (i : Fin 1 ⊕ Fin n) (j : Fin 1 ⊕ Fin m),
      π ^ e ∣ G t i j)
    (hpivot : ∃ a : (coefficientExtensionIntegers l E)ˣ,
      G t₀ (Sum.inl 0) (Sum.inl 0) = π ^ e * (a : coefficientExtensionIntegers l E)) :
    ∃ q : T → Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E),
      (∀ i j, @Continuous T (coefficientExtensionIntegers l E) _
        (coefficientExtensionIntegersTopology l E) (fun t ↦ q t i j)) ∧
      (∀ t i j, G t i j = π ^ e * q t i j) ∧
      IsUnit (q t₀ (Sum.inl 0) (Sum.inl 0)) := by
  classical
  let := spectralNorm.normedField (Padic l) E
  have hdata := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, hm0, _⟩
  have hm0' : coefficientExtensionMaximalIdeal l E ≠ ⊥ := hm0
  have hπ0 : π ≠ 0 := by
    intro h
    apply hm0'
    rw [← hπ, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hπE : (π : E) ≠ 0 := by
    intro h
    exact hπ0 (Subtype.ext h)
  let q : T → Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin m)
      (coefficientExtensionIntegers l E) := fun t i j ↦
    ⟨(G t i j : E) / (π : E) ^ e, by
      obtain ⟨a, ha⟩ := hdiv t i j
      have heq : (G t i j : E) = (π : E) ^ e * (a : E) := by
        exact_mod_cast ha
      rw [heq, mul_div_cancel_left₀ _ (pow_ne_zero e hπE)]
      exact a.property⟩
  have heq : ∀ t i j, G t i j = π ^ e * q t i j := by
    intro t i j
    apply Subtype.ext
    change (G t i j : E) = (π : E) ^ e * ((G t i j : E) / (π : E) ^ e)
    rw [mul_div_cancel₀ _ (pow_ne_zero e hπE)]
  refine ⟨q, ?_, heq, ?_⟩
  · intro i j
    change Continuous (fun t ↦ q t i j)
    exact ((continuous_subtype_val.comp (hG i j)).div_const _).subtype_mk _
  · obtain ⟨a, ha⟩ := hpivot
    have hqa : q t₀ (Sum.inl 0) (Sum.inl 0) = (a : coefficientExtensionIntegers l E) := by
      apply mul_left_cancel₀ (pow_ne_zero e hπ0)
      rw [← heq, ha]
    rw [hqa]
    exact a.isUnit

/-- Continuous unit-pivot elimination for the sum-index presentation of matrices.
This is the elementary Schur step used after continuous integral division.

Source: the auxiliary unit-pivot calculation for Hemo--Richarz--Scholbach,
Theorem 6.12(2), pp. 18--19 (blueprint: lem-sfb-unit-pivot-schur-formula).
Proof: use continuous uniformizer division at exponent zero for the open unit locus
and continuity of its inverse. Reindex the explicit `Fin (n+1)` Schur factors,
then transport their entrywise continuity, inverse continuity and block identity. -/
private theorem continuous_unit_pivot_splitting_sum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (T : Type v) [TopologicalSpace T] (m n : ℕ)
    (K : T → Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E))
    (hK : ∀ i j, @Continuous T (coefficientExtensionIntegers l E) _
      (coefficientExtensionIntegersTopology l E) (fun t ↦ K t i j))
    (t₀ : T) (hunit : IsUnit (K t₀ (Sum.inl 0) (Sum.inl 0))) :
    ∃ U : TopologicalSpace.Opens T, t₀ ∈ U ∧
      ∃ (L : U → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin n)
          (coefficientExtensionIntegers l E))
        (R : U → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin m)
          (coefficientExtensionIntegers l E))
        (H : U → Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E)),
        (∀ i j, @Continuous U (coefficientExtensionIntegers l E) _
          (coefficientExtensionIntegersTopology l E) (fun t ↦ L t i j)) ∧
        (∀ i j, @Continuous U (coefficientExtensionIntegers l E) _
          (coefficientExtensionIntegersTopology l E) (fun t ↦ (L t)⁻¹ i j)) ∧
        (∀ i j, @Continuous U (coefficientExtensionIntegers l E) _
          (coefficientExtensionIntegersTopology l E) (fun t ↦ R t i j)) ∧
        (∀ i j, @Continuous U (coefficientExtensionIntegers l E) _
          (coefficientExtensionIntegersTopology l E) (fun t ↦ (R t)⁻¹ i j)) ∧
        (∀ i j, @Continuous U (coefficientExtensionIntegers l E) _
          (coefficientExtensionIntegersTopology l E) (fun t ↦ H t i j)) ∧
        ∀ t : U,
          (L t : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n)
            (coefficientExtensionIntegers l E)) * K t *
            (R t : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m)
              (coefficientExtensionIntegers l E)) =
          Matrix.fromBlocks (fun (_i _j : Fin 1) ↦ 1) 0 0 (H t) := by
  classical
  rw [pivotTopology l E] at hK ⊢
  let := (coefficientExtensionAbsoluteValue l E).toNormedField
  let f : T → coefficientExtensionIntegers l E := fun t ↦ K t (Sum.inl 0) (Sum.inl 0)
  obtain ⟨q, _, hqeq, hlocal, _⟩ := (continuous_uniformizer_division l E 0).2
    f (hK (Sum.inl 0) (Sum.inl 0)) (by
      intro t
      exact ⟨f t, by simp⟩)
  have hqf : ∀ t, q t = f t := by
    intro t
    apply Subtype.ext
    simpa only [pow_zero, one_mul] using hqeq t
  obtain ⟨U, hU, ht₀, hUunit, hUinv⟩ := hlocal t₀ (by
    refine ⟨hunit.unit, ?_⟩
    simpa only [pow_zero, one_mul] using
      congrArg (fun x : coefficientExtensionIntegers l E ↦ (x : E)) hunit.unit_spec)
  let V : TopologicalSpace.Opens T := ⟨U, hU⟩
  have hunits : ∀ t : V, IsUnit (f t) := by
    intro t
    rw [← hqf]
    exact hUunit t t.property
  have hinv : Continuous (fun t : V ↦ Ring.inverse (f t)) := by
    apply continuous_induced_rng.mpr
    have hval : ∀ t : V,
        ((Ring.inverse (f t) : coefficientExtensionIntegers l E) : E) = (q t : E)⁻¹ := by
      intro t
      rw [hqf, Ring.inverse_of_isUnit (hunits t)]
      have hm := congrArg (fun x : coefficientExtensionIntegers l E ↦ (x : E))
        (hunits t).unit.inv_mul
      apply eq_inv_of_mul_eq_one_left
      simpa only [Subring.coe_mul, Subring.coe_one, (hunits t).unit_spec] using hm
    apply (continuousOn_iff_continuous_domRestrict.mp hUinv).congr
    intro t
    exact (hval t).symm
  let K' : V → Matrix (Fin (n + 1)) (Fin (m + 1)) (coefficientExtensionIntegers l E) :=
    fun t ↦ (K t).submatrix (pivotIndex n) (pivotIndex m)
  have hK' : ∀ i j, Continuous (fun t ↦ K' t i j) := by
    intro i j
    exact (hK (pivotIndex n i) (pivotIndex m j)).comp continuous_subtype_val
  obtain ⟨hlu, hru, hl, hr, hli, hri, hh, hid⟩ :=
    Matrix.continuous_unitPivot_schur_formula K' hK' hunits hinv
  let L : V → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin n)
      (coefficientExtensionIntegers l E) := fun t ↦
    Units.map (Matrix.reindexRingEquiv (coefficientExtensionIntegers l E)
      (pivotIndex n)).toMonoidHom (hlu t).unit
  let R : V → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin m)
      (coefficientExtensionIntegers l E) := fun t ↦
    Units.map (Matrix.reindexRingEquiv (coefficientExtensionIntegers l E)
      (pivotIndex m)).toMonoidHom (hru t).unit
  have hL (t : V) :
      (L t : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) (coefficientExtensionIntegers l E)) =
        (Matrix.unitPivotLeft (K' t)).submatrix (pivotIndex n).symm (pivotIndex n).symm := by
    dsimp [L]
  have hR (t : V) :
      (R t : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E)) =
        (Matrix.unitPivotRightElimination (K' t)).submatrix
          (pivotIndex m).symm (pivotIndex m).symm := by
    dsimp [R]
  have hLi (t : V) :
      ((L t)⁻¹).val =
        (Ring.inverse (Matrix.unitPivotLeft (K' t))).submatrix
          (pivotIndex n).symm (pivotIndex n).symm := by
    rw [← (hlu t).unit_spec, Ring.inverse_unit]
    rfl
  have hRi (t : V) :
      ((R t)⁻¹).val =
        (Ring.inverse (Matrix.unitPivotRightElimination (K' t))).submatrix
          (pivotIndex m).symm (pivotIndex m).symm := by
    rw [← (hru t).unit_spec, Ring.inverse_unit]
    rfl
  refine ⟨V, ht₀, L, R, (fun t ↦ Matrix.unitPivotSchurComplement (K' t)),
    ?_, ?_, ?_, ?_, hh, ?_⟩
  · intro i j
    simpa only [hL, Matrix.submatrix_apply] using
      hl ((pivotIndex n).symm i) ((pivotIndex n).symm j)
  · intro i j
    simpa only [hLi, Matrix.submatrix_apply] using
      hli ((pivotIndex n).symm i) ((pivotIndex n).symm j)
  · intro i j
    simpa only [hR, Matrix.submatrix_apply] using
      hr ((pivotIndex m).symm i) ((pivotIndex m).symm j)
  · intro i j
    simpa only [hRi, Matrix.submatrix_apply] using
      hri ((pivotIndex m).symm i) ((pivotIndex m).symm j)
  · intro t
    rw [hL, hR]
    have hKt : K t = (K' t).submatrix (pivotIndex n).symm (pivotIndex m).symm := by
      apply Matrix.ext
      intro i j
      simp only [K', Matrix.submatrix_apply, Equiv.apply_symm_apply]
    rw [hKt, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hid]
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl

/-- A continuous integral matrix whose entries are divisible by `π ^ e`, with the first
entry a unit times `π ^ e` at `t₀`, admits a continuous local integral pivot splitting.
The inverse changes of basis are also entrywise continuous. The residual sizes `n`, `m`
may be zero. No constancy assumption on any cokernel is made.

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, proof of Theorem 6.12(2),
finite extension case, pp. 18–19; agent continuous integral pivot variant
(blueprint: lem-sfb-continuous-integral-pivot-splitting).

Proof: (1) Divide every entry of `G` by `π ^ e`. Divisibility and continuous uniformizer
 division give a continuous integral matrix `q` with `G = π ^ e • q`. The first entry of
 `q` is a unit at `t₀`. Shrink to its open unit locus `U`, where its inverse is continuous.
(2) Apply the explicit unit-pivot Schur formula to `q` on `U`: first use the column
 transvection `R₀`, then the row transvection `L₁`, and finally scale the first row by
 the inverse pivot using `L₀`. The combined factor is `L₀ * L₁`. These matrices and their
 inverses have continuous entries, and give the block matrix with corner `1` and
 continuous residual block `H₀`.
(3) Rescale this identity by `π ^ e`, retain `L = L₀ * L₁` and `R = R₀`, and set
 `H = π ^ e • H₀`. This gives the stated block identity and continuity of `H`.
(4) If either residual index set is empty, interpret the same formulas as empty blocks.
 The finite matrix products and continuity assertions still hold, including the `1 × 1`
 case. These four steps are the proof recorded in the DAG. -/
theorem continuous_integral_pivot_splitting
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (T : Type v) [TopologicalSpace T] (m n : ℕ)
    (G : T → Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E))
    (hG : ∀ (i : Fin 1 ⊕ Fin n) (j : Fin 1 ⊕ Fin m),
      @Continuous T (coefficientExtensionIntegers l E) _
        (coefficientExtensionIntegersTopology l E) (fun t ↦ G t i j))
    (e : ℕ) (t₀ : T)
    (hdiv : ∀ (t : T) (i : Fin 1 ⊕ Fin n) (j : Fin 1 ⊕ Fin m), π ^ e ∣ G t i j)
    (hpivot : ∃ a : (coefficientExtensionIntegers l E)ˣ,
      G t₀ (Sum.inl 0) (Sum.inl 0) = π ^ e * (a : coefficientExtensionIntegers l E)) :
    ∃ U : TopologicalSpace.Opens T, t₀ ∈ U ∧
      ∃ (L : U → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin n) (coefficientExtensionIntegers l E))
        (R : U → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E))
        (H : U → Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E)),
        (∀ i j : Fin 1 ⊕ Fin n,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ L t i j)) ∧
        (∀ i j : Fin 1 ⊕ Fin n,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ (L t)⁻¹ i j)) ∧
        (∀ i j : Fin 1 ⊕ Fin m,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ R t i j)) ∧
        (∀ i j : Fin 1 ⊕ Fin m,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ (R t)⁻¹ i j)) ∧
        (∀ (i : Fin n) (j : Fin m),
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ H t i j)) ∧
        ∀ t : U,
          (L t : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) (coefficientExtensionIntegers l E)) *
            G t.val *
            (R t : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E)) =
          Matrix.fromBlocks
            (fun (_i _j : Fin 1) ↦ π ^ e) 0 0 (H t) := by
  let := spectralNorm.normedField (Padic l) E
  obtain ⟨q, hq, hqeq, hqunit⟩ := continuous_integral_pivot_division
    l E π hπ T m n G hG e t₀ hdiv hpivot
  obtain ⟨U, hU, L, R, H₀, hL, hLi, hR, hRi, hH, hident⟩ :=
    continuous_unit_pivot_splitting_sum l E T m n q hq t₀ hqunit
  refine ⟨U, hU, L, R, (fun t ↦ π ^ e • H₀ t), hL, hLi, hR, hRi, ?_, ?_⟩
  · intro i j
    exact continuous_const.mul (hH i j)
  · intro t
    rw [show G t.val = π ^ e • q t.val by
      apply Matrix.ext
      intro i j
      exact hqeq t.val i j]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hident t]
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, smul_eq_mul]

end Padic
