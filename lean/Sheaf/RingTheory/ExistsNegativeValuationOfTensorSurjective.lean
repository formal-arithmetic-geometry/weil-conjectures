/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.RingTheory.DVRValuationRingCharacterization

/-!
# Tensor surjectivity detects a negative discrete valuation

Source: Stacks Project, Varieties, Lemma 09N5, induction base case
(blueprint: lem-sc-dvr-tensor-surjective-negative-valuation).
-/

@[expose] public section

universe u

namespace IsDiscreteValuationRing

/-- Source: Stacks Project, Varieties, Lemma 09N5, induction base case
(blueprint: lem-sc-dvr-tensor-surjective-negative-valuation).
The tensor product is over `ℤ`, and its canonical map sends `a ⊗ b` to `a * b` in `K`.
The normalized additive valuation is `-WithZero.log` of the maximal-ideal adic valuation:
a uniformizer has multiplicative value `WithZero.exp (-1)`, hence additive value `1`.

Proof: Choose a uniformizer `t` of `B`. Its inverse has additive valuation `-1` and is
not in `B` (lem-sc-dvr-valuation-ring-characterization). Tensor surjectivity expresses
`t⁻¹` as a finite sum of products `a_j * b_j`. If all nonzero elements of `A` had
nonnegative valuation, then every nonzero product would have nonnegative valuation
by lem-sc-dvr-valuation-arithmetic and lem-sc-dvr-valuation-ring-characterization.
The Mathlib theorem `IsDiscreteValuationRing.exists_lift_of_le_one`, after converting
the additive inequality to the multiplicative valuation inequality, puts these products
in `B`; zero products also belong to `B`. Their sum belongs to `B`, a contradiction.
Thus some nonzero `a_j` has negative valuation. -/
theorem exists_negative_valuation_of_tensor_surjective {K : Type u} [Field K]
    (A B : Subring K) [IsFractionRing A K] [IsDiscreteValuationRing B]
    [IsFractionRing B K]
    (h : Function.Surjective
      (Algebra.TensorProduct.productMap A.subtype.toIntAlgHom B.subtype.toIntAlgHom)) :
    ∃ x : A, x ≠ 0 ∧ -WithZero.log ((maximalIdeal B).valuation K (x : K)) < 0 := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hgen : IsLocalRing.maximalIdeal B = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have hchar := dvr_valuation_ring_characterization B K
  let z : K := (algebraMap B K t)⁻¹
  have hzneg : -WithZero.log ((maximalIdeal B).valuation K z) = -1 := by
    simpa [z] using (hchar.2 t hgen).2
  have ht0 : algebraMap B K t ≠ 0 := by
    intro hzero
    have : t = 0 := (IsFractionRing.injective B K) (by simpa using hzero)
    exact ht.ne_zero this
  have hz0 : z ≠ 0 := inv_ne_zero ht0
  have hznmem : z ∉ Set.range (algebraMap B K) := by
    intro hz
    obtain ⟨b, hb⟩ := hz
    by_cases hb0 : b = 0
    · subst b
      simp at hb
      exact hz0 hb.symm
    · have hbn := hchar.1 b hb0
      rw [hb] at hbn
      linarith [hzneg]
  by_contra hn
  push Not at hn
  have hsum : ∀ q : TensorProduct ℤ A B,
      (Algebra.TensorProduct.productMap A.subtype.toIntAlgHom B.subtype.toIntAlgHom) q
        ∈ Set.range (algebraMap B K) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero]
        exact ⟨0, by simp⟩
    | tmul a b =>
        by_cases ha : a = 0
        · subst a
          refine ⟨0, ?_⟩
          simp
        · by_cases hb : b = 0
          · subst b
            refine ⟨0, ?_⟩
            simp
          · have ha' : 0 ≤ -WithZero.log ((maximalIdeal B).valuation K (a : K)) :=
              hn a ha
            have hb' := hchar.1 b hb
            have hab0 : ((a : K) * (b : K)) ≠ 0 :=
              mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
            have hb'' : 0 ≤ -WithZero.log
                ((maximalIdeal B).valuation K ((b : K))) := by
              change 0 ≤ -WithZero.log
                ((maximalIdeal B).valuation K (algebraMap B K b))
              exact hb'
            have hmul : 0 ≤ -WithZero.log
                ((maximalIdeal B).valuation K ((a : K) * (b : K))) := by
              rw [Valuation.map_mul, WithZero.log_mul]
              · nlinarith [ha', hb'']
              · simpa using ha
              · simpa using hb
            have hlog : ((maximalIdeal B).valuation K ((a : K) * (b : K))).log ≤ 0 := by
              linarith
            have hmult : (maximalIdeal B).valuation K ((a : K) * (b : K)) ≤ 1 := by
              rw [← WithZero.exp_zero]
              exact (WithZero.log_le_iff_le_exp (by simpa using hab0)).mp hlog
            obtain ⟨c, hc⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hmult
            exact ⟨c, by simpa using hc⟩
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        refine ⟨a + b, ?_⟩
        simp only [map_add]
        rw [← ha, ← hb]
  obtain ⟨q, hq⟩ := h z
  have := hsum q
  rw [hq] at this
  exact hznmem this

end IsDiscreteValuationRing
