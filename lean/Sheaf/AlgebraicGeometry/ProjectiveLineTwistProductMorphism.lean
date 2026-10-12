/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # The pointwise multiplication morphism of twists

Source: Stacks Project, Constructions, Equation 27.10.1.1 and Tag 01MS.
(blueprint: lem-sc-p1-twist-product-morphism).
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Twisting sections multiply pointwise through the sheaf tensor product.

Source: Stacks Project, Constructions, Equation 27.10.1.1 and Tag 01MS;
Step 2 of lem-sc-p1-twist-multiplication.
(blueprint: lem-sc-p1-twist-product-morphism).

Proof: For each open U multiply two twisting sections pointwise in each prime
localization. Their product has degree n+m, by the graded multiplication rule.
Local homogeneous fraction representatives multiply to a homogeneous fraction
representative, so this is a section. This operation is bilinear over the
structure sheaf and commutes with restriction, by the ring laws in each
localization. The tensor universal property gives a morphism from the tensor
product of the two underlying presheaves into the degree n+m twisting presheaf.
Apply the sheafification adjunction and the canonical identification of the
sheaf tensor product with the sheafification of the presheaf tensor product.
The adjunction unit equation says the resulting morphism on tmulSection is
exactly the pointwise product with which we started. This works in every degree,
including zero and negative degrees, without choosing any isomorphism or basis. -/
theorem projectiveLine_twist_product_morphism (k : Type u) [Field k] :
    ∃ μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m),
      (∀ (n m : ℤ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
        (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, U))
        (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U),
        (((μ n m).app U (tmulSection s t)).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * (t.1 x)) := by sorry

end AlgebraicGeometry
