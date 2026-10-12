module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ProjPolynomialTwistChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
@[expose] public section
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The nonvanishing locus of a homogeneous section is the corresponding standard open.
Source: Stacks Project, Constructions, Tags 01MS, 01MV and 01NG.
Proof: The coordinate opens D_+(x_i) cover polynomial Proj. On this chart O(d) has
basis x_i^d, and the section induced by f has coefficient f/x_i^d. Its value in the
one-dimensional residue-field fibre is nonzero if and only if that coefficient
is outside the corresponding prime of the degree-zero localization. By the
standard-open dictionary this means the homogeneous prime does not contain f,
exactly membership in D_+(f). The equality on all charts gives equality of sets.
For f=0 both sets are empty, including for positive d.
(blueprint: lem-sc-p1-homogeneous-section-tensor-powers-locus) -/
theorem proj_homogeneous_section_tensor_powers_locus (k : Type u) [Field k]
    {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    let L := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ))
    ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f :
        (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens) : Set _) =
        nonvanishingLocus L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) := by
  sorry
end AlgebraicGeometry
