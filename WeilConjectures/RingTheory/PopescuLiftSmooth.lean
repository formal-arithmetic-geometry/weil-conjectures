/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.RingTheory.PopescuLiftSmoothAway
import WeilConjectures.RingTheory.PopescuLiftSmoothSpecial

/-! # Smoothness of the explicit Popescu quotient

The prepared lifting algebra `d.liftingAlgebra` is smooth after inverting `π`, and smooth at
the primes of its special fibre lying over the smooth locus of `Cbar`.

## References

* [Stacks, Tag 07CP] (the key equality and the comparison with `D_k`)
-/

@[expose] public section

universe a c

namespace Algebra

/-- The prepared quotient, with the specified generator map, has all three smoothness
properties. -/
theorem popescu_lift_smooth (R : Type a) (Cbar : Type c)
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
    (∀ q : PrimeSpectrum d.liftingAlgebra,
      algebraMap R d.liftingAlgebra π ∉ q.asIdeal → IsSmoothAtPrime R q) ∧
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
  refine ⟨?_, popescu_lift_smooth_special R Cbar π d hd hAnnR c cmod hc hcmod⟩
  intro q hq
  exact ⟨algebraMap R d.liftingAlgebra π, hq,
    popescu_lift_smooth_away R Cbar π d hd⟩

end Algebra
