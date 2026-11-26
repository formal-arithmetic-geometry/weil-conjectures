/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.RingTheory.PopescuZeroBaseSingleChartPresentation
import WeilConjectures.RingTheory.PolynomialLinearElimination

/-! # Eliminating auxiliary variables in a single chart

After a scalar extension killing `π` and inverting `a_k`, the quotient by a single chart's
equations is a polynomial algebra over the localized reduced coefficient quotient.

## Implementation details

Only one chart's equations are used: no other chart's relations, conormal basis, smoothness or
differential basis is needed.

## References

* [Stacks, Tag 07CP] (the displayed calculation of `(D_k / π D_k)_{a_k}`)
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

/-- The single-chart quotient becomes a polynomial algebra when pi is killed. -/
theorem zero_base_single_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (hnorm : ∀ (k : Fin d.r) (l : Fin d.m), l ∈ d.E k →
      ∀ j : Fin d.m, d.h k l j = if l = j then d.a k else 0)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    Nonempty (MvPolynomial (d.E k)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
        Localization.Away (d.reducedElement k)) ≃ₐ[B]
      Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k)))))) := by
  classical
  dsimp only
  let K := B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
    Localization.Away (d.reducedElement k)
  let γ := d.singleChartCoefficient B k
  have ha : IsUnit (γ (d.a k)) := by
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (d.reducedElement k)) (d.reducedElement k)).map
        (Algebra.TensorProduct.includeRight
          (R := R ⧸ Ideal.span ({π ^ 2} : Set R)) (A := B)).toRingHom
  obtain ⟨u, hu⟩ := ha
  have hn : ∀ l : d.E k, ∀ j : d.E k,
      γ (d.h k l j) = if l = j then (u : K) else 0 := by
    intro l j
    rw [hnorm k l l.property j]
    by_cases hij : l = j
    · subst j
      simpa using hu.symm
    · have hij' : (l : Fin d.m) ≠ (j : Fin d.m) := by
        intro he
        exact hij (Subtype.ext he)
      simp [hij, hij']
  obtain ⟨e⟩ := MvPolynomial.linear_elimination K (Fin d.m) (d.E k) u
    (fun l j ↦ γ (d.h k l j)) hn
  obtain ⟨e'⟩ := zero_base_single_chart_presentation R Cbar π d B hπ k
  rw [hu] at e
  exact ⟨(e.restrictScalars B).trans e'⟩

end Algebra.PopescuLiftPresentation
