module

public import Sheaf.RingTheory.PopescuLiftPartialChart
import Sheaf.RingTheory.PopescuLiftChartComparison
import WeilConjectures.RingTheory.AnnihilatorElementFlatBaseChange

/-! # Flatness transferred from a partial Popescu chart

Source: Stacks Project, Tag 07CP, the final annihilator and local comparison argument.
(blueprint: lem-weil-pbc-popescu-lift-chart-maps-flat).
-/

@[expose] public section

universe a c

namespace Algebra.PopescuLiftPresentation

/--
Source: Stacks Project, Tag 07CP, the local comparison and localization steps.
(blueprint: lem-weil-pbc-popescu-lift-chart-maps-flat).

Apply flat base change of annihilators to pi and pi squared in the flat partial
chart local ring T. The base annihilator equality therefore gives the same
equality in T. The proved chart_comparison_bijective theorem identifies T with
the full chart local ring, so the comparison homomorphism is flat. The contraction
of the prime in the partial chart equals its contraction through the full chart,
by chartMap.commutes. Give T its algebra structure over the corresponding
localization of R, and check the scalar tower with localRingHom_to_map. Flatness
over that localization is equivalent to flatness over R. Compose its flat local
map with the flat comparison map; localRingHom_comp and chartMap.commutes identify
the composite with the desired canonical local ring homomorphism.
-/
theorem chart_maps_flat_of_partial {R : Type a} {Cbar : Type c}
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] [IsNoetherianRing R]
    (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (hAnnR : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)))
    (qD : PrimeSpectrum d.liftingAlgebra) (k : Fin d.r)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal
      (d.includeX (d.a k))) ∉ qD.asIdeal)
    (hpartial : Module.Flat R (d.chartLocal k qD)) :
    (Localization.localRingHom
      (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal
      qD.asIdeal (algebraMap R d.liftingAlgebra) rfl).Flat := by
  let T := d.chartLocal k qD
  have hflat : (algebraMap R T).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    exact hpartial
  have ha1 := RingHom.annihilator_element_flat_base_change
    (algebraMap R T) hflat π
  have ha2 := RingHom.annihilator_element_flat_base_change
    (algebraMap R T) hflat (π ^ 2)
  have hAnnT : Module.annihilator T (Ideal.span
      ({algebraMap R T π} : Set T)) = Module.annihilator T (Ideal.span
      ({(algebraMap R T π) ^ 2} : Set T)) := by
    calc
      _ = Ideal.map (algebraMap R T)
          (Module.annihilator R (Ideal.span ({π} : Set R))) := ha1
      _ = Ideal.map (algebraMap R T)
          (Module.annihilator R (Ideal.span ({π ^ 2} : Set R))) := by
        rw [hAnnR]
      _ = Module.annihilator T (Ideal.span
          ({algebraMap R T (π ^ 2)} : Set T)) := ha2.symm
      _ = _ := by rw [map_pow]
  have hbij := d.chart_comparison_bijective π hd k qD hk hAnnT
  have hcomp : (Localization.localRingHom (d.chartPrime k qD).asIdeal qD.asIdeal
      (d.chartMap k).toRingHom rfl).Flat := RingHom.Flat.of_bijective hbij
  have hpEq : (PrimeSpectrum.comap (algebraMap R (d.chartAlgebra k))
      (d.chartPrime k qD)).asIdeal =
      (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal := by
    ext r
    change d.chartMap k (algebraMap R (d.chartAlgebra k) r) ∈ qD.asIdeal ↔
      algebraMap R d.liftingAlgebra r ∈ qD.asIdeal
    rw [(d.chartMap k).commutes]
  have hpEq' : (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal =
      Ideal.comap (algebraMap R (d.chartAlgebra k)) (d.chartPrime k qD).asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal] using hpEq.symm
  have hbaseD : (Localization.localRingHom
      (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal
      (d.chartPrime k qD).asIdeal (algebraMap R (d.chartAlgebra k)) hpEq').Flat := by
    algebraize [algebraMap R (d.chartAlgebra k),
      Localization.localRingHom _ _ (algebraMap R (d.chartAlgebra k)) hpEq']
    have htower : IsScalarTower R
        (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal)
        (d.chartLocal k qD) := .of_algebraMap_eq fun x ↦
      (Localization.localRingHom_to_map _ _ (algebraMap R (d.chartAlgebra k)) hpEq' x).symm
    rw [RingHom.Flat]
    rw [Module.flat_iff_of_isLocalization
      (S := Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal)
      (p := (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal.primeCompl)]
    exact hpartial
  have htot := RingHom.Flat.comp hbaseD hcomp
  rw [← Localization.localRingHom_comp] at htot
  have heq : (d.chartMap k).toRingHom.comp (algebraMap R (d.chartAlgebra k)) =
      algebraMap R d.liftingAlgebra := by
    ext x
    exact congrArg ULift.down ((d.chartMap k).commutes x)
  simpa only [heq] using htot

end Algebra.PopescuLiftPresentation
