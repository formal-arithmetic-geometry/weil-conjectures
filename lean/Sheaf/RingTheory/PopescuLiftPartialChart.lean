/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.EquationCountFibreDimensionFlat
import Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension
import Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension

/-! # The partial equation chart in Popescu lifting

Source: Stacks Project, Tag 07CP, the presentation and equation count for D_k.
(blueprint: lem-weil-pbc-popescu-lift-partial-chart-dimension).
-/

@[expose] public section

noncomputable section

universe a c

namespace Algebra.PopescuLiftPresentation

variable {R : Type a} {Cbar : Type c} [CommRing R] [CommRing Cbar] {π : R}
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]

/-- One equation per auxiliary variable: u_l on E_k, and p_kl on its complement. -/
def chartEquation (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (l : Fin d.m) : d.polynomial :=
  if l ∈ d.E k then d.equation (.inl l) else d.equation (.inr (k, l))

abbrev chartIdeal (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  Ideal.span (Set.range (d.chartEquation k))

/-- The partial chart is an explicit quotient, with no chosen existence witness. -/
abbrev chartAlgebra (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  ULift.{c} (d.polynomial ⧸ d.chartIdeal k)

/-- Each partial-chart relation is a relation of the full lifting algebra. -/
theorem chartIdeal_le (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :
    d.chartIdeal k ≤ d.definingIdeal := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨l, rfl⟩
  unfold chartEquation
  split <;> exact Ideal.subset_span ⟨_, rfl⟩

/-- The canonical quotient map from the partial chart to the lifting algebra. -/
def chartMap (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :
    d.chartAlgebra k →ₐ[R] d.liftingAlgebra :=
  (ULift.algEquiv (R := R)).symm.toAlgHom.comp
    ((Ideal.Quotient.liftₐ (d.chartIdeal k) (Ideal.Quotient.mkₐ R d.definingIdeal)
      (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (d.chartIdeal_le k hx))).comp
        (ULift.algEquiv (R := R)).toAlgHom)

abbrev chartPrime (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (q : PrimeSpectrum d.liftingAlgebra) :=
  PrimeSpectrum.comap (d.chartMap k).toRingHom q

abbrev chartLocal (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (q : PrimeSpectrum d.liftingAlgebra) :=
  Localization.AtPrime (d.chartPrime k q).asIdeal

/-- The cleared relations give the key identity between the two types of equation. -/
theorem equation_key_identity [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (l : Fin d.m) :
    MvPolynomial.C π * d.equation (.inr (k, l)) =
      -d.includeX (d.a k) * d.equation (.inl l) +
        ∑ j ∈ d.E k, d.includeX (d.h k l j) * d.equation (.inl j) := by
  have hrel := congrArg d.includeX (hd.relation k l)
  simp only [map_mul, map_add, map_sum] at hrel
  rw [show d.includeX (MvPolynomial.C (π ^ 2)) = (MvPolynomial.C π) ^ 2 by
    change (MvPolynomial.rename Sum.inl) (MvPolynomial.C (π ^ 2)) = _
    rw [MvPolynomial.rename_C, MvPolynomial.C_pow]] at hrel
  have hsum : (∑ j ∈ d.E k, d.includeX (d.h k l j) *
      (d.includeX (d.f j) - MvPolynomial.C π * MvPolynomial.X (.inr j))) =
    (∑ j ∈ d.E k, d.includeX (d.h k l j) * d.includeX (d.f j)) -
      MvPolynomial.C π *
        (∑ j ∈ d.E k, d.includeX (d.h k l j) * MvPolynomial.X (.inr j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [equation]
  rw [hsum]
  change MvPolynomial.C π * _ = _
  change d.includeX (d.a k) * d.includeX (d.f l) =
    (∑ j ∈ d.E k, d.includeX (d.h k l j) * d.includeX (d.f j)) +
      (MvPolynomial.C π) ^ 2 * d.includeX (d.g k l) at hrel
  linear_combination hrel

/-- Invertibility of a_k and the key identity kill every original equation locally. -/
theorem chart_original_equation_eq_zero [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    (l : Fin d.m) :
    algebraMap (d.chartAlgebra k) (d.chartLocal k q)
      (ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inl l)))) = 0 := by
  classical
  let T := d.chartLocal k q
  let ev : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  have hchart (j : Fin d.m) : ev (d.chartEquation k j) = 0 := by
    have hq : Ideal.Quotient.mk (d.chartIdeal k) (d.chartEquation k j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
    change algebraMap (d.chartAlgebra k) T
      ((ULift.algEquiv (R := R)).symm (Ideal.Quotient.mk _ (d.chartEquation k j))) = 0
    rw [hq, map_zero, map_zero]
  have hu (j : Fin d.m) (hj : j ∈ d.E k) : ev (d.equation (.inl j)) = 0 := by
    simpa only [chartEquation, if_pos hj] using hchart j
  change ev (d.equation (.inl l)) = 0
  by_cases hl : l ∈ d.E k
  · exact hu l hl
  have hp : ev (d.equation (.inr (k, l))) = 0 := by
    simpa only [chartEquation, if_neg hl] using hchart l
  have hid := congrArg ev (d.equation_key_identity hd k l)
  simp only [map_mul, map_add, map_neg, map_sum] at hid
  have hsum : (∑ j ∈ d.E k, ev (d.includeX (d.h k l j)) *
      ev (d.equation (.inl j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hu j hj, mul_zero]
  have hmul : ev (d.includeX (d.a k)) * ev (d.equation (.inl l)) = 0 := by
    apply neg_eq_zero.mp
    rw [← neg_mul]
    rw [hp, mul_zero, hsum, add_zero] at hid
    exact hid.symm
  have hunit : IsUnit (ev (d.includeX (d.a k))) :=
    IsLocalization.map_units T
      (⟨ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.includeX (d.a k))), by
        change (d.chartMap k) _ ∉ q.asIdeal
        exact hk⟩ : (d.chartPrime k q).asIdeal.primeCompl)
  exact hunit.mul_right_eq_zero.mp hmul

/-- Every other chart's equation is killed by pi in the partial chart local ring. -/
theorem chart_other_equation_pi_mul_eq_zero [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    (k' : Fin d.r) (l : Fin d.m) :
    algebraMap R (d.chartLocal k q) π *
      algebraMap (d.chartAlgebra k) (d.chartLocal k q)
        (ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inr (k', l))))) = 0 := by
  let T := d.chartLocal k q
  let ev : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  have hu (j : Fin d.m) : ev (d.equation (.inl j)) = 0 :=
    d.chart_original_equation_eq_zero hd k q hk j
  have hid := congrArg ev (d.equation_key_identity hd k' l)
  simp only [map_mul, map_add, map_neg, map_sum] at hid
  have hsum : (∑ j ∈ d.E k', ev (d.includeX (d.h k' l j)) *
      ev (d.equation (.inl j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hu j, mul_zero]
  rw [hu l, mul_zero, hsum, zero_add] at hid
  exact hid

/-- The same m chart equations, with the variables numbered by Fin(n+m). -/
def finiteChartEquation (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (l : Fin d.m) : MvPolynomial (Fin (d.n + d.m)) R :=
  MvPolynomial.rename finSumFinEquiv (d.chartEquation k l)

abbrev finiteChartAlgebra (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  MvPolynomial (Fin (d.n + d.m)) R ⧸ Ideal.span (Set.range (d.finiteChartEquation k))

/-- Renumbering variables identifies the finite presentation with the partial chart. -/
def finiteChartEquiv (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :
    d.finiteChartAlgebra k ≃ₐ[R] d.chartAlgebra k :=
  (Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R finSumFinEquiv).symm
    (by
      rw [Ideal.map_span]
      change Ideal.span (Set.range (d.chartEquation k)) = _
      apply congrArg Ideal.span
      rw [← Set.range_comp']
      apply congrArg Set.range
      funext l
      change d.chartEquation k l = (MvPolynomial.renameEquiv R finSumFinEquiv).symm
        ((MvPolynomial.renameEquiv R finSumFinEquiv) (d.chartEquation k l))
      exact ((MvPolynomial.renameEquiv R finSumFinEquiv).symm_apply_apply _).symm)).trans
    (ULift.algEquiv (R := R)).symm

/-- The smooth special fibre of the partial chart has dimension n at the chosen prime.

Source: Stacks Project, Tag 07CP (lemma-lifting), the calculation of D_k/pi D_k.
(blueprint: lem-weil-pbc-popescu-lift-partial-chart-dimension).

Proof: On E_k the normalized p_kl vanish identically. Modulo pi and after inverting
 a_k, the cleared relations identify the original-variable quotient with
(Cbar/pi Cbar) localized at a_k. Solve p_kl for z_l outside E_k to identify the
special-fibre chart with a polynomial algebra over that quotient in |E_k| variables.
Smoothness of the prepared chart survives reduction modulo pi and base change to
the residue field at the contraction of q. Base change and localization of
differentials, followed by the polynomial extension decomposition, give rank
(n-|E_k|)+|E_k|=n, using Prepared.card_le. The smooth-over-field dimension lemma
identifies this with topologicalKrullDimAt of the fibre prime. Renumbering variables
and ULift do not change the fibre or its prime: they are the explicit equivalence
finiteChartEquiv. This proves the displayed dimension equality. No flatness or
equality of annihilators is used in this calculation. -/
theorem partial_chart_fibre_dimension [Algebra R Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal) :
    let q' := PrimeSpectrum.comap (d.finiteChartEquiv k).toRingHom (d.chartPrime k q)
    let p := PrimeSpectrum.comap (algebraMap R (d.finiteChartAlgebra k)) q'
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R (d.finiteChartAlgebra k) p ⟨q', rfl⟩) =
        (d.n : WithBot ℕ∞) := by sorry

/-- Apply equation-count flatness to the finite presentation of the partial chart.

Source: Stacks Project, Tag 07CP, applying Tag 00ST to D_k.
(blueprint: lem-weil-pbc-popescu-lift-partial-chart-dimension). -/
theorem partial_chart_flat [Algebra R Cbar] [IsNoetherianRing R]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal) :
    Module.Flat R (d.chartLocal k q) := by
  let e := d.finiteChartEquiv k
  let q' := PrimeSpectrum.comap e.toRingHom (d.chartPrime k q)
  have hdim := d.partial_chart_fibre_dimension hd k q hπ hk
  have hflat : Module.Flat R (Localization.AtPrime q'.asIdeal) :=
    (MvPolynomial.exists_flat_away_of_fibre_dimension_eq R (d.n + d.m) d.m
      (Nat.le_add_left _ _) (d.finiteChartEquation k) q'
      (by simpa only [Nat.add_sub_cancel] using hdim)).2.1
  let el := IsLocalization.ringEquivOfRingEquiv (M := q'.asIdeal.primeCompl)
    (T := (d.chartPrime k q).asIdeal.primeCompl)
    (Localization.AtPrime q'.asIdeal) (d.chartLocal k q) e.toRingEquiv
    (e.toRingEquiv.map_primeCompl_comap_eq (d.chartPrime k q).asIdeal)
  let eA : Localization.AtPrime q'.asIdeal ≃ₐ[R] d.chartLocal k q :=
    AlgEquiv.ofRingEquiv (f := el) fun r ↦ by
      dsimp only [el]
      rw [IsScalarTower.algebraMap_apply R (d.finiteChartAlgebra k)
        (Localization.AtPrime q'.asIdeal), IsLocalization.ringEquivOfRingEquiv_eq]
      change algebraMap (d.chartAlgebra k) (d.chartLocal k q)
        (e (algebraMap R (d.finiteChartAlgebra k) r)) = _
      rw [e.commutes, ← IsScalarTower.algebraMap_apply R (d.chartAlgebra k)
        (d.chartLocal k q)]
  exact Module.Flat.of_linearEquiv eA.symm.toLinearEquiv

end Algebra.PopescuLiftPresentation
