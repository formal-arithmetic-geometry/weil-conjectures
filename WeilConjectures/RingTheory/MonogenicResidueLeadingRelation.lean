/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Residue relation with nonvanishing leading coefficient

If `S = R[x]` and `m` is a maximal ideal of `S`, then `x` satisfies modulo `m` a positive-degree
relation over `R` whose leading coefficient is not in `m`.

## Implementation details

The residue of `x` generates `S/m` over `κ(m ∩ R)`, so it is algebraic by Zariski's lemma; the
minimal polynomial, scaled by a common denominator and lifted to `R`, gives the relation.

## References

* [Stacks, Tag 0334] (step 5)
-/

@[expose] public section

universe u v

/-- A residue generator satisfies a positive-degree relation whose leading coefficient
is not in the maximal ideal. -/
theorem exists_monogenic_residue_leading_relation
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B] (x : B)
    (m : Ideal (Algebra.adjoin R ({x} : Set B))) [m.IsMaximal] :
    ∃ p : Polynomial R, 0 < p.natDegree ∧
      algebraMap R (Algebra.adjoin R ({x} : Set B)) p.leadingCoeff ∉ m ∧
      Polynomial.aeval
        (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
          Algebra.adjoin R ({x} : Set B)) p ∈ m  := by
  classical
  let S := Algebra.adjoin R ({x} : Set B)
  let k := S ⧸ m
  let : Field k := Ideal.Quotient.field m
  let n : Ideal R := m.comap (algebraMap R S)
  let : n.IsPrime := inferInstance
  let A := R ⧸ n
  let F := FractionRing A
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite
    (Set.finite_singleton x)
  let : Algebra.FiniteType R k := inferInstance
  let i : A →+* k := Ideal.quotientMap m (algebraMap R S) le_rfl
  have hi : Function.Injective i := Ideal.algebraMap_quotient_injective
  let : Algebra A k := i.toAlgebra
  let : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra F k := (IsFractionRing.lift (K := F) (g := i) hi).toAlgebra
  let : IsScalarTower A F k := IsScalarTower.of_algebraMap_eq'
    (by
      ext a
      exact (IsFractionRing.lift_algebraMap (K := F) (g := i) hi a).symm)
  let : Algebra.FiniteType A k := Algebra.FiniteType.of_restrictScalars_finiteType R A k
  let : Algebra.FiniteType F k := Algebra.FiniteType.of_restrictScalars_finiteType A F k
  let : Module.Finite F k := finite_of_finite_type_of_isJacobsonRing F k
  let : Algebra.IsAlgebraic A k := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic F k)
  let xS : S := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  obtain ⟨q, hq, hqx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A)
    (Ideal.Quotient.mk m xS)
  obtain ⟨p, hp, hdeg⟩ := Polynomial.exists_natDegree_eq_of_mem_lifts
    (Polynomial.map_surjective (Ideal.Quotient.mk n) Ideal.Quotient.mk_surjective q)
  have hpos : 0 < q.natDegree := Polynomial.natDegree_pos_of_aeval_root hq hqx
    (fun a ha ↦ hi (ha.trans (map_zero i).symm))
  refine ⟨p, hdeg ▸ hpos, ?_, ?_⟩
  · intro hmem
    have hzero : Ideal.Quotient.mk n p.leadingCoeff = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    apply Polynomial.leadingCoeff_ne_zero.mpr hq
    change q.coeff q.natDegree = 0
    rw [← hdeg, ← hp, Polynomial.coeff_map]
    exact hzero
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    have eqeval : Polynomial.aeval (Ideal.Quotient.mk m xS)
        (p.map (Ideal.Quotient.mk n)) =
        Ideal.Quotient.mk m (Polynomial.aeval xS p) := by
      change Polynomial.aeval (Ideal.Quotient.mk m xS)
        (p.map (algebraMap R A)) = _
      rw [Polynomial.aeval_map_algebraMap]
      exact Polynomial.aeval_algHom_apply
        (Ideal.Quotient.mkₐ R m) xS p
    rw [hp] at eqeval
    exact eqeval.symm.trans hqx

