module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# A nonzero integral remainder from fractional rational coordinates

Source: Stacks Project, Algebra, Tag 07DQ, proof of `algebra-lemma-matrix-left-inverse`,
the adjugate identities; the floor-remainder refinement is supplied by the DAG proof
(blueprint: lem-trf-integer-matrix-fractional-lattice-witness).
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

/-- The columns of a nonsingular integer matrix are rationally independent. An integer vector
outside their integer span has unique rational coordinates, and subtracting the integer floors
of these coordinates gives a nonzero integer remainder with coefficients in `[0, 1)`, at least
one of which is strictly positive.

Source: Stacks Project, Algebra, Tag 07DQ, proof of `algebra-lemma-matrix-left-inverse`,
the adjugate identities. The fractional-coordinate refinement is the agent-supplied DAG proof
(blueprint: lem-trf-integer-matrix-fractional-lattice-witness).

Proof plan:
1. Write `δ = det A` and `B = adjugate A`. The adjugate identities give `BA = AB = δ I`.
   Map these identities to the rationals. Since `δ` is nonzero, `C = δ⁻¹ B` is a two-sided
   rational inverse to `A`.
2. Applying `C` to a rational relation among the columns makes every coefficient zero.
   For an integer vector `y`, set `b = Cy`. Then `Ab = y`, and applying `C` to any other
   solution proves uniqueness.
3. Set `z i = floor (b i)` and `a i = b i - z i`. The floor inequalities, also for negative
   coordinates, give `z i ≤ b i < z i + 1` and `0 ≤ a i < 1`.
4. The vector `x = y - Az` has integer entries, and its rational image equals
   `A(b - z) = Ab - Az = y - Az = x`. If `x = 0`, then `y = Az`, contrary to the
   outside-span hypothesis. Thus `x ≠ 0`; hence some `a j ≠ 0`, and its nonnegativity
   makes it strictly positive, while step 3 gives `a j < 1`. -/
theorem integer_fractional_lattice_witness (r : ℕ) (hr : 1 ≤ r)
    (A : Matrix (Fin r) (Fin r) ℤ) (hA : A.det ≠ 0) :
    LinearIndependent ℚ (fun j : Fin r ↦ fun i : Fin r ↦ (A i j : ℚ)) ∧
      ∀ y : Fin r → ℤ, (¬ ∃ m : Fin r → ℤ, A.mulVec m = y) →
        ∃ b : Fin r → ℚ,
          (A.map (Int.castRingHom ℚ)).mulVec b = (fun i ↦ (y i : ℚ)) ∧
          (∀ b' : Fin r → ℚ,
            (A.map (Int.castRingHom ℚ)).mulVec b' = (fun i ↦ (y i : ℚ)) → b' = b) ∧
          (∀ i : Fin r, (⌊b i⌋ : ℚ) ≤ b i ∧ b i < (⌊b i⌋ : ℚ) + 1) ∧
          (fun i ↦ ((y - A.mulVec (fun k ↦ ⌊b k⌋)) i : ℚ)) =
            (A.map (Int.castRingHom ℚ)).mulVec (fun i ↦ b i - (⌊b i⌋ : ℚ)) ∧
          y - A.mulVec (fun i ↦ ⌊b i⌋) ≠ 0 ∧
          (∀ i : Fin r, 0 ≤ b i - (⌊b i⌋ : ℚ) ∧ b i - (⌊b i⌋ : ℚ) < 1) ∧
          ∃ j : Fin r, 0 < b j - (⌊b j⌋ : ℚ) ∧ b j - (⌊b j⌋ : ℚ) < 1 := by
  classical
  by_cases hr0 : r = 0
  · subst r
    exact False.elim (Nat.not_succ_le_zero 0 hr)
  let M : Matrix (Fin r) (Fin r) ℚ := A.map (Int.castRingHom ℚ)
  have hM : M.det ≠ 0 := by
    dsimp only [M]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    change (A.det : ℚ) ≠ 0
    exact Int.cast_ne_zero.mpr hA
  let C : Matrix (Fin r) (Fin r) ℚ := M.det⁻¹ • M.adjugate
  have hCM : C * M = 1 := by
    dsimp [C]
    rw [Matrix.smul_mul, adjugate_mul, smul_smul, inv_mul_cancel₀ hM, one_smul]
  have hMC : M * C = 1 := by
    dsimp [C]
    rw [Matrix.mul_smul, mul_adjugate, smul_smul, inv_mul_cancel₀ hM, one_smul]
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    have h := congrArg C.mulVec huv
    simpa only [mulVec_mulVec, hCM, one_mulVec] using h
  refine ⟨linearIndependent_cols_of_det_ne_zero hM, ?_⟩
  intro y hy
  let b : Fin r → ℚ := C.mulVec (fun i ↦ (y i : ℚ))
  have hb : M.mulVec b = (fun i ↦ (y i : ℚ)) := by
    dsimp [b]
    rw [mulVec_mulVec, hMC, one_mulVec]
  have hfloor : ∀ i : Fin r, (⌊b i⌋ : ℚ) ≤ b i ∧ b i < (⌊b i⌋ : ℚ) + 1 :=
    fun i ↦ ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have hfrac : ∀ i : Fin r,
      0 ≤ b i - (⌊b i⌋ : ℚ) ∧ b i - (⌊b i⌋ : ℚ) < 1 :=
    fun i ↦ ⟨sub_nonneg.mpr (hfloor i).1, sub_lt_iff_lt_add'.mpr (hfloor i).2⟩
  have hcast (z : Fin r → ℤ) :
      (fun i ↦ (A.mulVec z i : ℚ)) = M.mulVec (fun i ↦ (z i : ℚ)) := by
    ext i
    exact (Int.castRingHom ℚ).map_mulVec A z i
  have hrem : (fun i ↦ ((y - A.mulVec (fun k ↦ ⌊b k⌋)) i : ℚ)) =
      M.mulVec (fun i ↦ b i - (⌊b i⌋ : ℚ)) := by
    rw [show (fun i ↦ b i - (⌊b i⌋ : ℚ)) =
      b - (fun i ↦ (⌊b i⌋ : ℚ)) from rfl, mulVec_sub, hb]
    ext i
    simp only [Pi.sub_apply, Int.cast_sub]
    rw [congrFun (hcast (fun k ↦ ⌊b k⌋)) i]
  have hx : y - A.mulVec (fun i ↦ ⌊b i⌋) ≠ 0 := by
    intro hzero
    exact hy ⟨(fun i ↦ ⌊b i⌋), (sub_eq_zero.mp hzero).symm⟩
  have ha : (fun i ↦ b i - (⌊b i⌋ : ℚ)) ≠ 0 := by
    intro hzero
    apply hx
    ext i
    have hi := congrFun hrem i
    rw [hzero, mulVec_zero] at hi
    exact Int.cast_eq_zero.mp hi
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  refine ⟨b, hb, (fun b' hb' ↦ hinj (hb'.trans hb.symm)), hfloor, hrem, hx, hfrac, j, ?_⟩
  exact ⟨lt_of_le_of_ne (hfrac j).1 (Ne.symm hj), (hfrac j).2⟩

end Matrix
