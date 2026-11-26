/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.FieldTheory.ExistsPBasis
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis
import WeilConjectures.FieldTheory.PBasisZeroDifferentialCoefficients

/-!
# Vanishing differentials over a perfect field

Over a perfect field of characteristic `p`, the differential `da` of an element of an extension
field vanishes exactly when `a` is a `p`-th power.

## Implementation details

The proof uses a `p`-basis `(tᵢ)` of `K` over `K^p`: since `k ⊆ K^p`, the `dtᵢ` form a basis of
the differentials, and expanding `a` in the monomials of the `tᵢ` shows that `da = 0` forces all
nonconstant coefficients to vanish.

## References

* [Stacks, Tag 031W]
* [Stacks, Tag 07P1]
* [Stacks, Tag 07P2]
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

private theorem adjoin_pow_eq_range
    (p : ℕ) [Fact p.Prime] (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] [CharP k p] [CharP K p] [PerfectField k] :
    (IntermediateField.adjoin k (Set.range (fun x : K ↦ x ^ p))).toSubfield =
      (frobenius K p).fieldRange := by
  apply le_antisymm
  · change Subfield.closure _ ≤ _
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · rcases hx with ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := surjective_frobenius k p c
      refine ⟨algebraMap k K d, ?_⟩
      change (algebraMap k K d) ^ p = algebraMap k K c
      rw [← map_pow, ← hd]
      rfl
    · exact hx
  · rintro x ⟨y, rfl⟩
    exact IntermediateField.subset_adjoin k _ ⟨y, rfl⟩

/-- Over a perfect field `k` of prime characteristic `p`, the universal differential of
`a : K` vanishes exactly when `a` is a `p`-th power in the extension field `K`. -/
theorem D_eq_zero_iff_exists_pow_of_perfectField
    (p : ℕ) [Fact p.Prime] (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] [CharP k p] [PerfectField k] (a : K) :
    D k K a = 0 ↔ ∃ b : K, a = b ^ p := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  constructor
  · intro ha
    let _ : Algebra (ZMod p) K := ZMod.algebra _ _
    obtain ⟨I, t, b, hb⟩ := Field.exists_p_basis p K
    have hfields :
        (IntermediateField.adjoin (ZMod p) (Set.range (fun x : K ↦ x ^ p))).toSubfield =
          (IntermediateField.adjoin k (Set.range (fun x : K ↦ x ^ p))).toSubfield :=
      (adjoin_pow_eq_range p (ZMod p) K).trans (adjoin_pow_eq_range p k K).symm
    let e : (IntermediateField.adjoin (ZMod p) (Set.range (fun x : K ↦ x ^ p))) ≃+*
        (IntermediateField.adjoin k (Set.range (fun x : K ↦ x ^ p))) :=
      { Set.equivOfEq (congrArg (fun S : Subfield K ↦ (S : Set K)) hfields) with
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
    let b' := b.mapCoeffs e (fun _ _ ↦ rfl)
    have hb' : ∀ E, b' E = E.val.prod (fun i e ↦ t i ^ e) := by
      intro E
      rw [Module.Basis.mapCoeffs_apply]
      exact hb E
    obtain ⟨bd, hbd⟩ := exists_basis_differentials_of_pBasis p t ⟨b', hb'⟩
    let z : {E : I →₀ ℕ // ∀ i : I, E i < p} :=
      ⟨0, fun _ ↦ (Fact.out : p.Prime).pos⟩
    have hc : b'.repr a = Finsupp.single z (b'.repr a z) := by
      classical
      apply Finsupp.ext
      intro E
      by_cases hE : E = z
      · subst E
        simp
      · rw [Finsupp.single_eq_of_ne hE]
        apply pBasis_repr_eq_zero_of_D_eq_zero p t b' hb'
          bd hbd a ha E
        intro h
        apply hE
        exact Subtype.ext h
    have haz : a = ((b'.repr a z :
        IntermediateField.adjoin k (Set.range (fun x : K ↦ x ^ p))) : K) := by
      calc
        a = Finsupp.linearCombination _ b' (b'.repr a) :=
          (b'.linearCombination_repr a).symm
        _ = Finsupp.linearCombination _ b' (Finsupp.single z (b'.repr a z)) :=
          congrArg _ hc
        _ = (b'.repr a z) • b' z := Finsupp.linearCombination_single _ _ _
        _ = _ := by rw [hb']; simp [z, Algebra.smul_def]
    have hamem : a ∈ (frobenius K p).fieldRange := by
      rw [← adjoin_pow_eq_range p k K, haz]
      exact (b'.repr a z).property
    obtain ⟨c, hc⟩ := hamem
    exact ⟨c, hc.symm⟩
  · rintro ⟨b, rfl⟩
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero]
    simp

end KaehlerDifferential
