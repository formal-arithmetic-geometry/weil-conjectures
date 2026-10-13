module

public import Sheaf.RingTheory.PopescuLiftPresentation

@[expose] public section

universe a c

namespace Algebra

/-! # Descent of the special-chart substitution -/

/-- The polynomial elimination substitution descends to the unlocalized special
lifting quotient, as a homomorphism over the special coefficient ring.
Source: Stacks Project, Tag 07CP, polynomial elimination modulo pi and comparison
of chart coefficients.
(blueprint: lem-weil-pbc-popescu-special-chart-substitution).

Proof: Write A=(Cbar/pi)[1/a_k]. Substitute x_i by its coefficient class in A,
z_j for j in E_k by X_j, and z_l otherwise by a_k inverse times the sum of
h_klj X_j. The f_l vanish since the kernel of the prepared presentation is their
span. The k-th relations vanish by normalized_h. For a chart kprime, compare
its expansion of a_k a_kprime f_l with that on chart k in the localized reduced
conormal module. The prepared basis makes every coefficient
 a_kprime h_klj - sum h_kprime,ljprime h_k,jprimej
zero in the reduced coefficient chart. The surjective presentation and its
specified kernel identify that chart with Cbar[1/a_k]; passing to A preserves
these equalities. Thus all other chart relations vanish as well. Descend through
the defining quotient, ULift, and the quotient by pi. This gives the claimed
map and its values on the free variables. To check coefficient compatibility,
use hc for the x_i, algebra compatibility for constants, polynomial induction
and hd.surjective for Cbar, and hcmod for Cbar/pi. No nontriviality assumption
is needed: localization at zero and empty sets of free variables are allowed. -/
theorem popescu_special_chart_substitution (R : Type a) (Cbar : Type c)
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
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
    let D₀ := d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
    letI := cmod.toAlgebra
    let A := Localization.Away (Ideal.Quotient.mk
      (Ideal.span ({algebraMap R Cbar π} : Set Cbar)) (d.ε (d.reduced (d.a k))))
    ∃ g : D₀ →ₐ[C₀] MvPolynomial (d.E k) A,
      ∀ j : d.E k, g (Ideal.Quotient.mk _
        (ULift.up (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inr j.1))))) =
          MvPolynomial.X j := by
  sorry

end Algebra
