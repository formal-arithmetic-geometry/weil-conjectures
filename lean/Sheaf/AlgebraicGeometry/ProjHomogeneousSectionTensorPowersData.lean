module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication
import Sheaf.AlgebraicGeometry.ProjPolynomialTwistChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

@[expose] public section
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Tensor-power isomorphisms and multiplication identities for a homogeneous section.
Source: Stacks Project, Constructions, Tags 01MS, 01MU and 01NG; equation-multiply.
Proof: On D_+(x_i), the twist O(m) is free with basis x_i^m for every integer m.
Multiplication of homogeneous fractions maps the tensor of the bases to x_i^(m+r),
so the multiplication maps are isomorphisms and agree on overlaps. Starting with
O = O(0), iterate them to obtain a_n, and compose multiplication with id tensor a_n
to obtain b_mn. The local coefficient of the section f is f/x_i^d, whose nth tensor
power is (f/x_i^d)^n. The identifications therefore send the tensor-power section
and its product with any local section of O(m) to multiplication by f^n. Equality
on the chart cover proves both morphism identities globally. At n=0 these are the
unit isomorphisms and multiplication by 1; for f=0 positive powers are zero.
Negative m uses the same local basis and the fraction multiplication rule.
(blueprint: lem-sc-p1-homogeneous-section-tensor-powers-data) -/
theorem proj_homogeneous_section_tensor_powers_data (k : Type u) [Field k]
    {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    let L := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ))
    ∃ (a : ∀ n : ℕ, L.tensorPow n ≅
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (0 + ((n • d : ℕ) : ℤ)))
        (b : ∀ (m : ℤ) (n : ℕ),
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⊗ L.tensorPow n ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
              (m + ((n • d : ℕ) : ℤ))),
        (∀ n : ℕ, tensorPowSection
            (homOfGlobalSection L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
            n ≫ (a n).hom =
          Proj.unitToTwist (SetLike.pow_mem_graded n hf)) ∧
        (∀ (m : ℤ) (n : ℕ),
          (ρ_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)).inv ≫
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ◁
              tensorPowSection
                (homOfGlobalSection L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
                n ≫ (b m n).hom =
            Proj.twistMul m (SetLike.pow_mem_graded n hf)) := by
  sorry
end AlgebraicGeometry
