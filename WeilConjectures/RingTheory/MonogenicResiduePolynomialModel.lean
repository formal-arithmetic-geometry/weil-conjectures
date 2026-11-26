/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Basic
import WeilConjectures.RingTheory.MonogenicResidueLeadingRelation
import WeilConjectures.RingTheory.MonogenicPrincipalLocalizationModel

/-!
# Monic residue relation after a principal localization

If `S = R[x]` and `m` is a maximal ideal of `S`, then after localizing at a suitable nonzero
coefficient `a`, the presentation `S_a ≃ A[y]` carries a monic positive-degree relation for `y`
lying in the extension of `m`.

## Implementation details

The residue relation `p` with leading coefficient `a ∉ m` makes `a` a unit after localization, and
`f = c(a)⁻¹ · c(p)` is monic of the same positive degree.

## References

* [Stacks, Tag 0334] (step 5)
-/

@[expose] public section

universe u v

/-- A monic residue relation after a principal localization, before splitting its roots. -/
theorem exists_monogenic_residue_polynomial_model
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    ∃ (s : Algebra.adjoin R ({x} : Set K)), s ∉ m ∧
      ∃ (A L : Type (max u v)) (_ : CommRing A) (_ : IsDomain A)
        (_ : IsIntegrallyClosed A) (_ : Field L) (_ : Algebra A L)
        (_ : IsFractionRing A L),
        IsNagataRing A ∧ ∃ (y : L)
          (e : Localization.Away s ≃+* Algebra.adjoin A ({y} : Set L))
          (f : Polynomial A), f.Monic ∧ 0 < f.natDegree ∧
            Polynomial.aeval
              (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
                Algebra.adjoin A ({y} : Set L)) f ∈
              m.map (e.toRingHom.comp (algebraMap _ (Localization.Away s)))  := by
  classical
  obtain ⟨p, hp, hlead, heval⟩ := exists_monogenic_residue_leading_relation R K x m
  have ha : p.leadingCoeff ≠ 0 := by
    intro h
    apply hlead
    rw [h, map_zero]
    exact m.zero_mem
  obtain ⟨A, L, instCR, instD, instIC, instF, instA, instFR, hA, y, c, hc, hu,
      e, hcoef, hx⟩ := exists_monogenic_principal_localization_model R K hR x
        p.leadingCoeff ha
  let : CommRing A := instCR
  let : IsDomain A := instD
  let : IsIntegrallyClosed A := instIC
  let : Field L := instF
  let : Algebra A L := instA
  let : IsFractionRing A L := instFR
  let s := algebraMap R (Algebra.adjoin R ({x} : Set K)) p.leadingCoeff
  let q := p.map c
  let f := Polynomial.C (↑hu.unit⁻¹ : A) * q
  have hqdeg : q.natDegree = p.natDegree := Polynomial.natDegree_map_eq_of_injective hc p
  have hqlc : q.leadingCoeff = c p.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_injective hc p
  have hmonic : f.Monic := by
    change f.leadingCoeff = 1
    dsimp only [f]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hqlc]
    simpa only [hu.unit_spec] using Units.inv_mul hu.unit
  have hfdeg : f.natDegree = p.natDegree := by
    dsimp only [f]
    rw [Polynomial.natDegree_C_mul (Units.ne_zero hu.unit⁻¹), hqdeg]
  refine ⟨s, hlead, A, L, instCR, instD, instIC, instF, instA, instFR, hA, y, e, f,
    hmonic, hfdeg ▸ hp, ?_⟩
  let j := e.toRingHom.comp
    (algebraMap (Algebra.adjoin R ({x} : Set K)) (Localization.Away s))
  have hj : j (Polynomial.aeval
      (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
        Algebra.adjoin R ({x} : Set K)) p) =
      Polynomial.aeval
        (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
          Algebra.adjoin A ({y} : Set L)) q := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.hom_eval₂]
    congr 1
    ext r
    exact congrArg Subtype.val (hcoef r)
  have hmem := Ideal.mem_map_of_mem j heval
  rw [hj] at hmem
  dsimp only [f]
  rw [map_mul, Polynomial.aeval_C]
  exact Ideal.mul_mem_left _ _ hmem

