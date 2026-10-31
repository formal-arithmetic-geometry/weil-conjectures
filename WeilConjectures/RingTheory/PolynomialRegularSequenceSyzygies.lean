/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Mathlib.RingTheory.Regular.Flat
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial extensions of regular sequences and their first syzygies

Source: Stacks Project, Tags 0BIQ (polynomial-extension argument), 00LF, 062F,
and 0622/0623 (blueprint: lem-trf-polynomial-regular-sequence-syzygies).

The finite tuple module is `Fin s → MvPolynomial (Fin m) R`. Its standard vector
`fᵢ eⱼ` is `Pi.single j (MvPolynomial.C (f i))`; thus the displayed relation has
exactly the sign `fᵢ eⱼ - fⱼ eᵢ`. Only pairs with `i < j` occur in the sum.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory.Sequence

private theorem boundary_zero_formula {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (x : ⋀[R]^1 (Fin r →₀ R)) :
    exteriorPower.zeroEquiv R (Fin r →₀ R) (ExteriorAlgebra.koszulBoundary R r f 0 x) =
      Finsupp.linearCombination R f (exteriorPower.oneEquiv R (Fin r →₀ R) x) := by
  have he : (exteriorPower.zeroEquiv R (Fin r →₀ R)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary R r f 0) = (Finsupp.linearCombination R f).comp
        (exteriorPower.oneEquiv R (Fin r →₀ R)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    change exteriorPower.zeroEquiv R (Fin r →₀ R)
      (ExteriorAlgebra.koszulBoundary R r f 0 (exteriorPower.ιMulti R 1 v)) = _
    apply (exteriorPower.zeroEquiv R (Fin r →₀ R)).symm.injective
    simp only [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    simp [ExteriorAlgebra.koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
      ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
      Algebra.algebraMap_eq_smul_one]
  exact LinearMap.congr_fun he x

private theorem boundary_one_formula {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (v : Fin 2 → (Fin r →₀ R)) :
    exteriorPower.oneEquiv R (Fin r →₀ R)
        (ExteriorAlgebra.koszulBoundary R r f 1 (exteriorPower.ιMulti R 2 v)) =
      Finsupp.linearCombination R f (v 0) • v 1 -
        Finsupp.linearCombination R f (v 1) • v 0 := by
  apply (exteriorPower.oneEquiv R (Fin r →₀ R)).symm.injective
  simp only [LinearEquiv.symm_apply_apply, map_sub, map_smul]
  apply Subtype.ext
  simp [ExteriorAlgebra.koszulBoundary, exteriorPower.oneEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
    CliffordAlgebra.contractLeft_ι, Matrix.vecTail, Algebra.algebraMap_eq_smul_one]

private theorem syzygies_of_isKoszulRegular {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (hf : IsKoszulRegular f)
    (v : Fin r → R) (hv : ∑ i, f i * v i = 0) :
    ∃ b : Fin r → Fin r → R,
      v = ∑ i : Fin r, ∑ j ∈ Finset.univ.filter (fun j : Fin r ↦ i < j),
        b i j • (Pi.single j (f i) - Pi.single i (f j)) := by
  classical
  let e := Finsupp.linearEquivFunOnFinite R R (Fin r)
  let q := exteriorPower.oneEquiv R (Fin r →₀ R)
  let x := q.symm (e.symm v)
  let K := ExteriorAlgebra.koszulComplex R r f
  have hx : ExteriorAlgebra.koszulBoundary R r f 0 x = 0 := by
    apply (exteriorPower.zeroEquiv R (Fin r →₀ R)).injective
    rw [boundary_zero_formula, map_zero]
    simpa [x, q, e, Finsupp.linearCombination_eq_fintype_linearCombination_apply,
      Fintype.linearCombination_apply, mul_comm] using hv
  have he := (K.exactAt_iff_isZero_homology 1).mpr (hf 1 (by decide))
  have hex := (K.exactAt_iff' (i := 2) (j := 1) (k := 0)
    (by simp) (by simp)).mp he
  obtain ⟨w, hw⟩ := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mp hex x hx
  change ExteriorAlgebra.koszulBoundary R r f 1 w = x at hw
  let B := (Finsupp.basisSingleOne : Module.Basis (Fin r) R (Fin r →₀ R)).exteriorPower 2
  let a := B.repr w
  let t : Set.powersetCard (Fin r) 2 → Fin 2 ↪o Fin r :=
    fun p ↦ Set.powersetCard.ofFinEmbEquiv.symm p
  have ht (p : Set.powersetCard (Fin r) 2) : t p 0 < t p 1 :=
    (t p).strictMono (by decide)
  have hB (p : Set.powersetCard (Fin r) 2) :
      e (q (ExteriorAlgebra.koszulBoundary R r f 1 (B p))) =
        Pi.single (t p 1) (f (t p 0)) - Pi.single (t p 0) (f (t p 1)) := by
    dsimp only [B, q]
    rw [exteriorPower.basis_apply]
    simp only [exteriorPower.ιMulti_family, boundary_one_formula]
    ext i
    simp [e, t, Finsupp.basisSingleOne, Finsupp.single_apply, Pi.single_apply, mul_comm,
      eq_comm]
  have hcoord : v = ∑ p, a p •
      (Pi.single (t p 1) (f (t p 0)) - Pi.single (t p 0) (f (t p 1))) := by
    calc
      v = e (q (ExteriorAlgebra.koszulBoundary R r f 1 w)) := by
        rw [hw]
        simp [x]
      _ = e (q (ExteriorAlgebra.koszulBoundary R r f 1 (∑ p, a p • B p))) := by
        rw [show (∑ p, a p • B p) = w from B.sum_repr w]
      _ = _ := by simp only [map_sum, map_smul, hB]
  refine ⟨fun i j ↦ ∑ p, if t p 0 = i ∧ t p 1 = j then a p else 0, ?_⟩
  rw [hcoord]
  simp_rw [Finset.sum_smul]
  conv_rhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1
  funext p
  simp [ite_smul, ite_and, Finset.sum_ite_irrel, ht]

/-- A regular sequence stays regular after adjoining finitely many polynomial variables,
and every relation among the constant polynomials is a sum of the pairwise Koszul relations.
Source: Stacks Project, Tag 0BIQ, polynomial-extension argument; Tags 00LF, 062F,
and 0622/0623 (blueprint: lem-trf-polynomial-regular-sequence-syzygies).

Proof:
1. Regularity implies `R` is nontrivial. The polynomial ring is a nontrivial free
   `R`-module, with its monomial basis, and is therefore faithfully flat.
2. Apply Mathlib's `IsRegular.of_faithfullyFlat` and rewrite `List.map_ofFn`.
   This gives regularity of the sequence of constant polynomials, including the
   nonzero-final-quotient condition of `def-weil-pbc-regular-sequence`.
3. Apply `lem-weil-pbc-regular-sequence-koszul-regular` over the polynomial ring.
   By `def-weil-pbc-koszul-regular-sequence`, the first Koszul homology vanishes.
4. In `def-weil-pbc-koszul-complex`, `d₁(v) = ∑ fᵢ vᵢ` and
   `d₂(eᵢ ∧ eⱼ) = fᵢ eⱼ - fⱼ eᵢ` for `i < j`. By the kernel-modulo-image
   description of `def-weil-pbc-module-chain-complex-homology`, the given cycle
   is a boundary. Expand a preimage in the exterior-square basis and apply
   linearity to obtain the displayed sum. For `s = 1` the sum is empty and `v = 0`.
-/
theorem polynomial_regular_sequence_syzygies
    {R : Type u} [CommRing R] (s m : ℕ) (hs : 1 ≤ s) (f : Fin s → R)
    (hf : IsRegular R (List.ofFn f)) :
    IsRegular (R := MvPolynomial (Fin m) R) (MvPolynomial (Fin m) R)
        (List.ofFn (fun i : Fin s ↦ MvPolynomial.C (f i))) ∧
      ∀ v : Fin s → MvPolynomial (Fin m) R,
        (∑ i : Fin s, MvPolynomial.C (f i) * v i) = 0 →
          ∃ b : Fin s → Fin s → MvPolynomial (Fin m) R,
            v = ∑ i : Fin s, ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ i < j),
              b i j • (Pi.single j (MvPolynomial.C (f i)) -
                Pi.single i (MvPolynomial.C (f j))) := by
  have _hs : 1 ≤ s := hs
  let : Nontrivial R := hf.nontrivial
  have hreg : IsRegular (R := MvPolynomial (Fin m) R) (MvPolynomial (Fin m) R)
      (List.ofFn (fun i : Fin s ↦ MvPolynomial.C (f i))) := by
    simpa [List.map_ofFn, Function.comp_def] using
      (hf.of_faithfullyFlat (S := MvPolynomial (Fin m) R))
  refine ⟨hreg, ?_⟩
  exact syzygies_of_isKoszulRegular _ hreg.isKoszulRegular

end RingTheory.Sequence
