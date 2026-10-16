module

public import Sheaf.RingTheory.PopescuLiftPartialChart
import Sheaf.RingTheory.EquationCountFibreDimensionFlat

/-! # Equation-count flatness of the partial Popescu chart

Source: Stacks Project, Tag 07CP, the partial-chart equation count and Tag 00ST.
(blueprint: lem-weil-pbc-popescu-lift-chart-partial-flat-repair).
-/

@[expose] public section

universe a c

namespace Algebra.PopescuLiftPresentation

/--
Source: Stacks Project, Tag 07CP, equation-count flatness for the prepared partial chart.
(blueprint: lem-weil-pbc-popescu-lift-chart-partial-flat-repair).

The finite presentation of the partial chart has one equation for each auxiliary
variable.  The fibre dimension computation gives the expected dimension, so the
standard equation-count flatness theorem yields flatness of the localization at
the pulled-back prime.  This statement isolates that geometric calculation from
the comparison with the full lifting algebra.
-/
theorem partial_chart_flat_repair {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsNoetherianRing R]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal
      (d.includeX (d.a k))) ∉ q.asIdeal) :
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
