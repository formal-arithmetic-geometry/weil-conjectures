module

public import Sheaf.RingTheory.PopescuSpecialChartMap

@[expose] public section

universe a c

namespace Algebra

/-- The canonical special-chart map is injective.
Source: Stacks Project, Tag 07CP, polynomial elimination modulo pi
and comparison of the other chart relations.
(blueprint: lem-weil-pbc-popescu-special-chart-map-injective).

Proof: Put A = (Cbar/pi Cbar)[1/a_k]. Define a substitution from R[x,z] to
A[z_j : j in E_k] by sending x_i to its coefficient class, z_j for j in E_k
to X_j, and every other z_l to a_k inverse times sum h_klj X_j. The f_l
map to zero, and pi maps to zero. The k-th relations vanish by substitution,
including those indexed by E_k by normalized_h. For another chart k',
compare its expression for a_k a_k' f_l with the expression on chart k
in the localized reduced conormal module. Linear independence of the basis
specified by hd.conormal forces every coefficient
b_j = a_k' h_klj - sum h_k'lj' h_kj'j to vanish in the localized reduced
coefficient quotient. The presentation surjection and its specified kernel
identify this quotient with Cbar[1/a_k]. Mapping onwards to A preserves the
zero coefficients. Consequently substitution kills every other chart relation.
It therefore descends through the defining quotient, ULift, and the quotient
by pi, and extends through localization because the image of a_k is a unit.
Its composite with the canonical chart map fixes each X_j. It fixes the
coefficients too: hc identifies the x_i images, algebra-map compatibility
identifies constants, and polynomial induction followed by hd.surjective
identifies all of Cbar; hcmod then identifies Cbar/pi Cbar. The composite
fixes the inverse of a_k by uniqueness of inverses, so it fixes A. Polynomial
extensionality makes this composite the identity. A map with this left inverse
is injective, without any assumption that the coefficient rings are nontrivial. -/
theorem popescu_special_chart_map_injective (R : Type a) (Cbar : Type c)
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
    Function.Injective (popescu_special_chart_map R Cbar π d c cmod hcmod k) := by
  sorry

end Algebra
