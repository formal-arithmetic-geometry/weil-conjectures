/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.RingTheory.PopescuSpecialChartInjective
import WeilConjectures.RingTheory.PopescuSpecialChartSurjective

/-! # Polynomial model of a prepared lifting chart

The prepared special chart of the Popescu lifting algebra is a polynomial algebra over the
localized coefficient quotient.

## References

* [Stacks, Tag 07CP] (polynomial chart calculation and comparison of charts)
-/

@[expose] public section

universe a c b

namespace Algebra

/-- The prepared special chart is a polynomial algebra over the localized coefficient
quotient. -/
theorem popescu_special_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom)
    (k : Fin d.r) :
    let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
    letI := cmod.toAlgebra
    Nonempty (MvPolynomial (d.E k)
      (Localization.Away (Ideal.Quotient.mk
        (Ideal.span ({algebraMap R Cbar π} : Set Cbar)) (d.ε (d.reduced (d.a k))))) ≃ₐ[C₀]
      Localization.Away (c (d.ε (d.reduced (d.a k))))) := by
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let := cmod.toAlgebra
  exact ⟨AlgEquiv.ofBijective (popescu_special_chart_map R Cbar π d c cmod hcmod k)
    ⟨popescu_special_chart_map_injective R Cbar π d hd c cmod hc hcmod k,
      popescu_special_chart_map_surjective R Cbar π d c cmod hc hcmod k⟩⟩

end Algebra
