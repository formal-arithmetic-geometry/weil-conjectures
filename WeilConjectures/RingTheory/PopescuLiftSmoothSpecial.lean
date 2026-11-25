/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.RingTheory.PopescuLiftChartFibres
import WeilConjectures.RingTheory.PopescuLiftChartFlat

/-!
# Smoothness of the Popescu lifting algebra on the special fibre

The prepared lifting algebra is smooth at the primes of its special fibre lying over the smooth
locus of `Cbar`, using the partial charts `D_k`.

## References

* [Stacks, Tag 07CP] (construction of `D_k` and proof of properties (c), (d))
-/

@[expose] public section

universe a c

namespace Algebra

/-- The two special-fibre smoothness conclusions for the explicit prepared quotient. -/
theorem popescu_lift_smooth_special (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] [IsNoetherianRing R] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (hAnnR : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)))
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) :
    (∀ q : PrimeSpectrum (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)),
      IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R))
        (PrimeSpectrum.comap c.toRingHom q) →
      IsSmoothAtPrime R (PrimeSpectrum.comap (Ideal.Quotient.mk _) q)) ∧
    (∀ q : PrimeSpectrum (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)),
      IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R))
        (PrimeSpectrum.comap c.toRingHom q) →
      @IsSmoothAtPrime (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar))
        (d.liftingAlgebra ⧸
          Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra))
        _ _ cmod.toAlgebra q) := by
  rw [← forall_and]
  intro q
  rw [← imp_and]
  intro hq
  obtain ⟨k, hk⟩ := hd.cover (PrimeSpectrum.comap c.toRingHom q) hq
  obtain ⟨hfibre, hspecial⟩ :=
    popescu_lift_chart_fibres R Cbar π d hd c cmod hc hcmod q k hk
  have hflat := popescu_lift_chart_flat R Cbar π d hd hAnnR c hc q k hk
  have : FinitePresentation R d.liftingAlgebra := d.finitePresentation
  let qD : PrimeSpectrum d.liftingAlgebra :=
    PrimeSpectrum.comap (Ideal.Quotient.mk _) q
  have hfp : ∃ g : d.liftingAlgebra,
      g ∉ qD.asIdeal ∧
      FinitePresentation R (Localization.Away g) :=
    ⟨1, qD.isPrime.one_notMem,
      FinitePresentation.of_isLocalizationAway (1 : d.liftingAlgebra)⟩
  exact ⟨flat_smooth_fibre_smooth_at_prime (R := R)
    (S := d.liftingAlgebra) qD hfp hflat hfibre,
    c (d.ε (d.reduced (d.a k))), hk, hspecial⟩

end Algebra
