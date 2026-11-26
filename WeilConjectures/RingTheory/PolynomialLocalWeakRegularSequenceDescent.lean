/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

import WeilConjectures.RingTheory.PolynomialLocalIdealRelationFiniteStage

/-! # Finite-coefficient descent for localized weakly regular sequences

A sequence that is weakly regular in the localized polynomial rings over all finite type
coefficient subrings is weakly regular in `R[x]_Q`.

## Implementation details

The finite type subrings containing `R₀` form a directed system whose localized polynomial rings,
and prefix quotients, have colimit `R[x]_Q` and its prefix quotients. Exactness of filtered
colimits (Tag 00DB) preserves injectivity of multiplication by the next equation. No flatness of
the coefficient-subring inclusions is assumed.

## References

* [Stacks, Tag 00SV] (filtered-colimit paragraphs of the proof)
* [Stacks, Tag 00DB]
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

private theorem regular_quotient_iff_ideal_cancel
    {A : Type*} [CommRing A] (I : Ideal A) (a : A) :
    IsSMulRegular (A ⧸ (I • ⊤ : Submodule A A)) a ↔
      ∀ x : A, a * x ∈ I → x ∈ I := by
  change IsSMulRegular (A ⧸ (I * ⊤ : Ideal A)) a ↔ _
  rw [Ideal.mul_top]
  simpa only [smul_eq_mul] using
    (isSMulRegular_quotient_iff_mem_of_smul_mem (I : Submodule A A) a)

/-- Weak regularity in polynomial local rings passes from all finite type coefficient
subrings containing a fixed finite type subring to the full coefficient ring. -/
theorem isWeaklyRegular_polynomial_local_of_finiteType_subrings
    {R : Type u} [CommRing R] (R₀ : Subring R)
    (hR₀ : Algebra.FiniteType ℤ R₀) {n c : ℕ}
    (f₀ : Fin c → MvPolynomial (Fin n) R₀)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (hstage : ∀ (B : Subring R) (hB : R₀ ≤ B), Algebra.FiniteType ℤ B →
      IsWeaklyRegular
        (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)))
        ((List.ofFn (fun i ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ i))).map
          (algebraMap (MvPolynomial (Fin n) B)
            (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)))))) :
    IsWeaklyRegular (Localization.AtPrime Q)
      ((List.ofFn (fun i ↦ MvPolynomial.map R₀.subtype (f₀ i))).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))) := by
  constructor
  intro i hi
  apply (regular_quotient_iff_ideal_cancel _ _).mpr
  intro x hx
  have hic : i < c := by simpa using hi
  obtain ⟨B, hB, hft, φ, hφ, y, hy, hrel⟩ :=
    exists_finiteType_subring_local_ideal_relation R₀ hR₀
      ((List.ofFn f₀).take i) (f₀ ⟨i, hic⟩) Q x (by
        simpa only [List.getElem_map, List.getElem_ofFn, List.map_take,
          List.map_map, List.map_ofFn, Function.comp_def] using hx)
  have hreg := (hstage B hB hft).regular_mod_prev i (by simpa using hic)
  have hymem := (regular_quotient_iff_ideal_cancel _ _).mp hreg y (by
    simpa only [List.getElem_map, List.getElem_ofFn, List.map_take,
      List.map_map, List.map_ofFn, Function.comp_def] using hrel)
  have hmaps :
      (((List.ofFn (fun j ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ j))).map
        (algebraMap (MvPolynomial (Fin n) B)
          (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype))))).map φ) =
      ((List.ofFn (fun j ↦ MvPolynomial.map R₀.subtype (f₀ j))).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))) := by
    simp only [List.map_ofFn]
    congr 1
    funext j
    dsimp only [Function.comp_def]
    rw [hφ, MvPolynomial.map_map]
    rfl
  have hmem := Ideal.mem_map_of_mem φ hymem
  rw [Ideal.map_ofList, List.map_take, hmaps, hy] at hmem
  exact hmem

end RingTheory.Sequence
